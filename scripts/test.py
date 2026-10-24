#!/usr/bin/env python3
"""Run Claude Code on a Rocq benchmark case.

Configure the model in your shell, then run:
    python scripts/test.py --benchmark 001 --tag experiment --timeout 3600
"""

import argparse
import atexit
import fcntl
import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
import time
from pathlib import Path
from case_names import canonical_name, BY_NAME

ROOT = Path("/data0/zzh/PL-Paper-AutoProof")
CLAUDE_BINARY = Path("/data0/zzh/tools/claude-code/2.1.308/claude")
OUTPUT_ROOT = ROOT / "benchmarkResults"
WORKSPACE_ROOT = OUTPUT_ROOT / ".workspaces"
_ACTIVE_WORKSPACES = set()

def _save_trace(trace_dir, problem, raw_stdout):
    trace_dir.mkdir(parents=True, exist_ok=True)
    with (trace_dir / f"{problem}.jsonl").open("a") as stream:
        stream.write(raw_stdout)
        if raw_stdout and not raw_stdout.endswith("\n"):
            stream.write("\n")

def _session_id(raw_stdout):
    for line in raw_stdout.splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("session_id"):
            return event.get("session_id")
    return None

def _parse_result(raw_stdout):
    responses = {}
    for line in reversed(raw_stdout.splitlines()):
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("type") == "result":
            return _usage_metrics(event.get("usage", {}))
        if event.get("type") == "assistant":
            message = event.get("message", {})
            if message.get("id") and message.get("usage"):
                # Several content blocks can repeat the same response's usage.
                responses.setdefault(message["id"], message["usage"])
    if not responses:
        return _empty_metrics()
    # On timeout, count reported responses; an unfinished request may be missing.
    metrics = [_usage_metrics(usage) for usage in responses.values()]
    return {key: sum(item[key] for item in metrics) for key in metrics[0]}

def _usage_metrics(usage):
    cached = usage.get("cache_read_input_tokens", 0)
    created = usage.get("cache_creation_input_tokens", 0)
    inputs = usage.get("input_tokens", 0) + cached + created
    outputs = usage.get("output_tokens", 0)
    return {
        "input_tokens": inputs,
        "cached_input_tokens": cached,
        "cache_creation_input_tokens": created,
        "output_tokens": outputs,
        "total_tokens": inputs + outputs,
    }

def _empty_metrics():
    return dict.fromkeys(("input_tokens", "cached_input_tokens",
                         "cache_creation_input_tokens", "output_tokens", "total_tokens"))

def load_results(results_file):
    if not results_file.exists():
        return {}
    return json.loads(results_file.read_text())

def save_results(results, results_file):
    # Parallel cases merge under one lock; readers see only complete JSON.
    results_file.parent.mkdir(parents=True, exist_ok=True)
    with results_file.with_suffix(".lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        merged = load_results(results_file)
        merged.update(results)
        with tempfile.NamedTemporaryFile(mode="w", dir=results_file.parent,
                                         delete=False) as stream:
            json.dump(dict(sorted(merged.items())), stream, indent=2)
            stream.write("\n")
        os.replace(stream.name, results_file)

def private_claude_home(workspace):
    return workspace.parent / f".{workspace.name}.claude-home"

def cleanup_workspace(workspace):
    shutil.rmtree(private_claude_home(workspace), ignore_errors=True)
    shutil.rmtree(workspace, ignore_errors=True)
    _ACTIVE_WORKSPACES.discard(workspace)

def cleanup_active_workspaces():
    for workspace in list(_ACTIVE_WORKSPACES):
        cleanup_workspace(workspace)

def terminate_with_cleanup(signum, _frame):
    cleanup_active_workspaces()
    raise SystemExit(128 + signum)

def install_cleanup_handlers():
    atexit.register(cleanup_active_workspaces)
    signal.signal(signal.SIGTERM, terminate_with_cleanup)
    signal.signal(signal.SIGHUP, terminate_with_cleanup)

def isolated_command(workspace, command):
    """Run a command where only this case is visible below /workspace.

    The host filesystem is read-only.  The repository, sibling benchmark
    workspaces, and host /tmp are over-mounted with private empty filesystems.
    Claude Code receives a private configuration and session directory.
    """
    bwrap = shutil.which("bwrap")
    if not bwrap:
        raise RuntimeError("bubblewrap (bwrap) is required for isolated runs")
    claude_home = private_claude_home(workspace)
    claude_home_mount = "/mnt/claude-home"
    rocq_root = Path.home() / ".opam" / "rocq-dev"
    node_root = Path("/data1/zzh/node")
    args = [
        bwrap,
        "--die-with-parent", "--new-session",
        "--unshare-pid", "--unshare-ipc", "--unshare-uts", "--unshare-cgroup",
        "--ro-bind", "/", "/",
        "--tmpfs", str(Path.home()),
        "--tmpfs", "/tmp",
        "--tmpfs", "/mnt",
        "--dir", claude_home_mount,
        "--bind", str(claude_home), claude_home_mount,
        "--setenv", "CLAUDE_CONFIG_DIR", claude_home_mount,
        "--setenv", "DISABLE_AUTOUPDATER", "1",
    ]
    if rocq_root.is_dir():
        args += [
            "--dir", str(rocq_root.parent),
            "--dir", str(rocq_root),
            "--ro-bind", str(rocq_root), str(rocq_root),
        ]
    args += ["--tmpfs", str(node_root.parent)]
    if node_root.is_dir():
        args += [
            "--dir", str(node_root),
            "--ro-bind", str(node_root), str(node_root),
        ]
    args += [
        "--tmpfs", str(ROOT.parent),
        "--ro-bind", str(CLAUDE_BINARY.parent), str(CLAUDE_BINARY.parent),
        "--bind", str(workspace), "/workspace",
        "--proc", "/proc", "--dev", "/dev",
        "--chdir", "/workspace",
    ]
    return args + command

def prepare_workspace(benchmark, problem):
    """Copy exactly one problem into a private disposable workspace."""
    WORKSPACE_ROOT.mkdir(parents=True, exist_ok=True)
    workspace = Path(tempfile.mkdtemp(prefix=f"{problem}.", dir=WORKSPACE_ROOT))
    _ACTIVE_WORKSPACES.add(workspace)
    try:
        shutil.copy2(benchmark / "input" / "Task.v.orig", workspace / "Task.v")
        shutil.copy2(benchmark / "input" / "Task.v.orig", workspace / "Task.v.orig")
        shutil.copy2(benchmark / "card.md", workspace / "card.md")
        claude_home = private_claude_home(workspace)
        claude_home.mkdir(mode=0o700)
    except BaseException:
        cleanup_workspace(workspace)
        raise
    return workspace

def verify_isolation(workspace):
    """Fail closed if the private namespace exposes repository data."""
    probe = isolated_command(workspace, [
        "/bin/bash", "-c",
        "test -f /workspace/Task.v && "
        "test -f /workspace/card.md && "
        f"test ! -e {ROOT} && "
        f"test ! -e {WORKSPACE_ROOT} && "
        "test \"$CLAUDE_CONFIG_DIR\" = /mnt/claude-home && "
        "test ! -e /home/zzh/.claude && "
        "test ! -e /mnt/claude-home/projects && "
        "touch /workspace/.isolation-write-test"
    ])
    subprocess.run(probe, check=True, stdout=subprocess.DEVNULL,
                   stderr=subprocess.PIPE, text=True)
    (workspace / ".isolation-write-test").unlink()

def build_prompt(task_path, card_path, lr_first=False):
    card = card_path.read_text()
    prompt = f"""Target file: {task_path}

## Problem Card
{card}

## Instructions
Work offline: use only the supplied task and locally installed Rocq libraries.
Do not search the web, fetch external proofs, or access the internet through
shell commands or scripts (including curl, wget, git clone, and HTTP clients).

Edit Task.v directly and finish the target theorem. You may add definitions
and helper lemmas to Task.v. Do not modify Task.v.orig. Do not create a
separate solution file. Do not use Admitted, admit, Abort, Axiom, Parameter,
Conjecture, unsafe Rocq flags, or equivalent escape hatches. Compile Task.v
with Rocq and continue fixing errors until it succeeds.

Keep working until the target theorem is proved and Task.v compiles, or the
external runner stops you. The runner manages the time limit; do not assume
your budget is exhausted because the proof looks long or difficult.
Difficulty, a failed approach, or uncertainty about
the next step is not a reason to end the attempt. Make concrete proof edits,
compile them, and use the resulting goals and errors to guide the next attempt.
When stuck, isolate a smaller lemma, strengthen an induction hypothesis, or
reconsider the logical relation and proof strategy. Do not finish with a plan
or a failure report while the proof remains incomplete; continue proof work.
Reading the task and compiling its unfinished skeleton is not a proof attempt.
Turn your next proof idea into code and test it rather than merely describing
the lemmas that would be needed. If an approach fails, try a different one
instead of repeating the same unsuccessful commands.

If you are explicitly asked to stop or notified that the execution budget is
exhausted, report any unfinished proof honestly and briefly explain the main
capability bottleneck across the attempt and what would help overcome it.
Do not stop proof work merely to write this report."""
    if lr_first:
        prompt += """

Before proving, first carefully design a suitable logical relation. Check
that it supports the required proof obligations and is strong enough to
derive the target theorem.
If an obligation fails, revise the relation instead of patching tactics
locally."""
    return prompt

def run_agent(problem, workspace, timeout, trace_dir, lr_first=False, session_id=None):
    """Run one Claude Code turn; model configuration comes from the environment."""
    if session_id:
        prompt = """Continue the same proof attempt from your existing conversation and Task.v.
The runner has not accepted a completed proof. Preserve your progress; do not restart from
Task.v.orig. Inspect the current goals, make concrete proof edits, and compile.
Continue until the target is proved without proof escapes or the runner stops you.
All original task constraints still apply."""
    else:
        prompt = build_prompt(Path("/workspace/Task.v"), workspace / "card.md", lr_first)
    command = [
        str(CLAUDE_BINARY), "-p", "--output-format", "stream-json", "--verbose",
        "--dangerously-skip-permissions", "--setting-sources", "",
        "--strict-mcp-config", "--mcp-config", '{"mcpServers":{}}',
        "--disable-slash-commands",
        "--disallowedTools", "WebSearch,WebFetch",
    ]
    if session_id:
        command += ["--resume", session_id]
    start = time.monotonic()
    try:
        process = subprocess.run(
            isolated_command(workspace, command), input=prompt,
            capture_output=True, text=True, cwd=workspace, timeout=timeout,
        )
        stdout, stderr = process.stdout, process.stderr
        exit_status, returncode = "ok", process.returncode
    except subprocess.TimeoutExpired as exc:
        stdout, stderr = exc.stdout or b"", exc.stderr or b""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="replace")
        exit_status, returncode = "timeout", None
    _save_trace(trace_dir, problem, stdout)
    with (trace_dir / f"{problem}.stderr.log").open("a") as stream:
        stream.write(stderr)
    return {
        "exit": exit_status, "returncode": returncode,
        "elapsed": time.monotonic() - start, "metrics": _parse_result(stdout),
        "session_id": _session_id(stdout) or session_id,
    }

def run_until_done(problem, workspace, timeout, trace_dir,
                   lr_first=False, reject_admits=False):
    """Resume one private session until verified success or the shared deadline."""
    start = time.monotonic()
    deadline = start + timeout
    original = (workspace / "Task.v.orig").read_bytes()
    session_id = None
    metrics = _empty_metrics()
    raw = {"exit": "timeout", "returncode": None}
    compiled = False
    turns = 0
    trace_dir.mkdir(parents=True, exist_ok=True)
    for suffix in ("jsonl", "stderr.log"):
        (trace_dir / f"{problem}.{suffix}").write_text("")
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raw["exit"] = "timeout"
            break
        raw = run_agent(
            problem, workspace, remaining, trace_dir,
            lr_first=lr_first, session_id=session_id,
        )
        turns += 1
        session_id = raw["session_id"] or session_id
        # Each CLI invocation reports the usage of that invocation.
        for key, value in raw["metrics"].items():
            if value is not None:
                metrics[key] = (metrics[key] or 0) + value
        if (workspace / "Task.v.orig").read_bytes() != original:
            break
        remaining = deadline - time.monotonic()
        if raw["exit"] == "timeout" or remaining <= 0:
            raw["exit"] = "timeout"
            break
        compiled = check(workspace, reject_admits=reject_admits,
                         timeout=min(300, remaining))
        if compiled:
            raw.update(exit="ok", returncode=0)
            break
        if raw["returncode"] == 0 and not session_id:
            # Never silently replace an existing conversation with a fresh one.
            raw["returncode"] = 1
            print(f"[ERROR] {problem}: no session ID to resume", flush=True)
            break
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raw["exit"] = "timeout"
            break
        print(
            f"[CONTINUE] {problem}: turn {turns + 1}, "
            f"{int(remaining)}s remaining; preserving proof and session",
            flush=True,
        )
        if raw["returncode"] != 0:
            time.sleep(min(1, remaining))
    return {**raw, "elapsed": time.monotonic() - start,
            "metrics": metrics, "compiled": compiled, "turns": turns}

def has_proof_holes(source):
    """Reject explicit proof escapes, ignoring nested Rocq comments and strings."""
    code = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith('(*', i):
            depth += 1
            code.append(' ')
            i += 2
        elif depth and source.startswith('*)', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source[i] == '"':
            match = re.match(r'"(?:[^\"]|\"\")*"', source[i:])
            i += len(match[0]) if match else 1
            code.append(' ')
        else:
            code.append(source[i])
            i += 1
    return bool(re.search(
        r'\b(?:Admitted|admit|give_up|Axioms?|Parameters?|Conjectures?)\b',
        ''.join(code),
    ))


def check(workspace, reject_admits=False, timeout=300):
    """Return whether Task.v compiles inside the isolated namespace."""
    if not (workspace / 'Task.v').is_file():
        return False
    if reject_admits and has_proof_holes((workspace / 'Task.v').read_text()):
        return False
    rocq = Path.home() / ".opam" / "rocq-dev" / "bin" / "rocq"
    try:
        r = subprocess.run(
            isolated_command(workspace, [str(rocq), "compile", "-q", "Task.v"]),
            capture_output=True, text=True, cwd=workspace, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False
    return r.returncode == 0

def main():
    install_cleanup_handlers()
    parser = argparse.ArgumentParser(description="Run a Rocq benchmark case")
    parser.add_argument(
        "--benchmark", required=True,
        help="Case ID (001), full name, or legacy name",
    )
    parser.add_argument("--tag", required=True, help="Tag for results/proofs")
    parser.add_argument("--lr-first", action="store_true")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--reject-admits", action="store_true",
                        help="Also reject explicit admissions and added axiom/parameter commands")
    parser.add_argument("--output-root", type=Path, default=OUTPUT_ROOT)
    parser.add_argument("--benchmark-root", type=Path, default=ROOT / "benchmarks",
                        help="Input directory; defaults to the standard benchmark collection")
    args = parser.parse_args()

    requested = args.benchmark
    args.benchmark = canonical_name(requested)
    benchmark = args.benchmark_root / args.benchmark
    if not benchmark.is_dir():
        legacy = BY_NAME.get(args.benchmark, {}).get("old_name", requested)
        benchmark = args.benchmark_root / legacy
    result_dir = args.output_root / args.benchmark
    results_file = args.output_root / f"results_{args.tag}.json"
    proof_dir = result_dir / f"proofs_{args.tag}"
    trace_dir = result_dir / f"traces_{args.tag}"

    previous = load_results(results_file).get(args.benchmark)
    if previous is None:
        previous = load_results(result_dir / results_file.name).get(args.benchmark)
        if previous is not None:
            save_results({args.benchmark: previous}, results_file)
    if previous is not None and previous.get("status") != "agent_error":
        print(
            f"[SKIP] {args.benchmark}: {previous.get('status', 'completed')}",
            flush=True,
        )
        return

    result_dir.mkdir(parents=True, exist_ok=True)
    proof_dir.mkdir(parents=True, exist_ok=True)
    trace_dir.mkdir(parents=True, exist_ok=True)

    print(f"Case:    {args.benchmark}")
    print(f"Results: {results_file}")
    print(f"Proofs:  {proof_dir}/")
    print(f"Traces:  {trace_dir}/")

    workspace = prepare_workspace(benchmark, args.benchmark)
    task_file = workspace / "Task.v"
    original = (workspace / "Task.v.orig").read_bytes()
    print(f"Isolated workspace: {workspace}")
    try:
        verify_isolation(workspace)
        raw = run_until_done(
            args.benchmark, workspace, args.timeout, trace_dir,
            lr_first=args.lr_first,
            reject_admits=args.reject_admits,
        )
        proof_path = proof_dir / "Task.v"
        if task_file.exists():
            shutil.copy2(task_file, proof_path)
        compiled = raw["compiled"]
        orig_untouched = (workspace / "Task.v.orig").read_bytes() == original

        if raw["exit"] == "timeout":
            status = "timeout"
        elif raw["returncode"] != 0:
            status = "agent_error"
        elif not orig_untouched:
            status = "invalid_modified_orig"
        else:
            status = "proved" if compiled else "failed"

        result = {
            "status": status,
            "time_s": int(raw["elapsed"]),
            "turns": raw["turns"],
            **raw["metrics"],
        }
        save_results({args.benchmark: result}, results_file)
        print(
            f"[DONE] {args.benchmark}: {status} "
            f"({int(raw['elapsed'])}s)",
            flush=True,
        )
    finally:
        cleanup_workspace(workspace)


if __name__ == "__main__":
    main()
