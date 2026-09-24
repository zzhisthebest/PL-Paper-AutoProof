#!/usr/bin/env python3
"""Run Codex on a Rocq benchmark case.

Usage:
    python scripts/test.py --benchmark stlc --tag codex
    python scripts/test.py --benchmark systemf --tag codex \
        --model MODEL --reasoning-effort high
    python scripts/test.py --benchmark stlc --tag qwen \
        --model qwen3.8-27b-local \
        --local-base-url http://127.0.0.1:8200/v1
"""

import argparse, atexit, json, os, signal, subprocess, time, shutil, tempfile
from pathlib import Path

ROOT = Path("/data0/zzh/PL-Paper-AutoProof")
OUTPUT_ROOT = Path("/data0/zzh/benchmarkResults")
WORKSPACE_ROOT = OUTPUT_ROOT / ".workspaces"
_ACTIVE_WORKSPACES = set()

def _save_trace(trace_dir, problem, raw_stdout):
    trace_dir.mkdir(parents=True, exist_ok=True)
    (trace_dir / f"{problem}.jsonl").write_text(raw_stdout)

def _archive_failed_attempt(trace_dir, problem, attempt):
    for suffix in ("jsonl", "stderr.log"):
        source = trace_dir / f"{problem}.{suffix}"
        if source.exists():
            shutil.copy2(
                source,
                trace_dir / f"{problem}.attempt-{attempt}.{suffix}",
            )

def _parse_result(raw_stdout):
    for line in reversed(raw_stdout.strip().split('\n')):
        try:
            evt = json.loads(line)
        except json.JSONDecodeError:
            continue
        if evt.get('type') in {'turn.completed', 'result'}:
            usage = evt.get('usage', {})
            input_tokens = usage.get('input_tokens')
            output_tokens = usage.get('output_tokens')
            return {
                'input_tokens': input_tokens,
                'cached_input_tokens': usage.get('cached_input_tokens'),
                'output_tokens': output_tokens,
                'total_tokens': (
                    input_tokens + output_tokens
                    if input_tokens is not None and output_tokens is not None
                    else None
                ),
            }
    return _empty_metrics()

def _empty_metrics():
    return {
        'input_tokens': None,
        'cached_input_tokens': None,
        'output_tokens': None,
        'total_tokens': None,
    }

def load_results(results_file):
    if not results_file.exists():
        return {}
    return json.loads(results_file.read_text())

def save_results(results, results_file):
    results_file.write_text(json.dumps(results, indent=2) + "\n")

def private_codex_home(workspace):
    return workspace.parent / f".{workspace.name}.codex-home"

def cleanup_workspace(workspace):
    shutil.rmtree(private_codex_home(workspace), ignore_errors=True)
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
    Codex receives a fresh private home containing authentication but no user
    configuration, plugins, histories, sessions, or previous traces.
    """
    bwrap = shutil.which("bwrap")
    if not bwrap:
        raise RuntimeError("bubblewrap (bwrap) is required for isolated runs")
    codex_home = private_codex_home(workspace)
    codex_home_mount = "/mnt/codex-home"
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
        "--dir", codex_home_mount,
        "--bind", str(codex_home), codex_home_mount,
        "--setenv", "CODEX_HOME", codex_home_mount,
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
        codex_home = private_codex_home(workspace)
        codex_home.mkdir(mode=0o700)
        auth_file = Path.home() / ".codex" / "auth.json"
        if auth_file.is_file():
            shutil.copy2(auth_file, codex_home / "auth.json")
            (codex_home / "auth.json").chmod(0o600)
    except BaseException:
        cleanup_workspace(workspace)
        raise
    return workspace

def reset_workspace(workspace):
    """Restore a clean task before retrying an agent infrastructure error."""
    for child in workspace.iterdir():
        if child.name in {"Task.v.orig", "card.md"}:
            continue
        if child.is_dir():
            shutil.rmtree(child)
        else:
            child.unlink()
    shutil.copy2(workspace / "Task.v.orig", workspace / "Task.v")

def verify_isolation(workspace):
    """Fail closed if the private namespace exposes repository data."""
    probe = isolated_command(workspace, [
        "/bin/bash", "-c",
        "test -f /workspace/Task.v && "
        "test -f /workspace/card.md && "
        f"test ! -e {ROOT} && "
        f"test ! -e {WORKSPACE_ROOT} && "
        "test \"$CODEX_HOME\" = /mnt/codex-home && "
        "test ! -e /home/zzh/.codex && "
        "test ! -e /mnt/codex-home/history.jsonl && "
        "test ! -e /mnt/codex-home/sessions && "
        "touch /workspace/.isolation-write-test"
    ])
    subprocess.run(probe, check=True, stdout=subprocess.DEVNULL,
                   stderr=subprocess.PIPE, text=True)
    (workspace / ".isolation-write-test").unlink()

def build_prompt(task_path, card_path, lr_first=False, given_r=False):
    card = card_path.read_text()
    prompt = f"""Target file: {task_path}

## Problem Card
{card}

## Instructions
Edit Task.v directly and finish the target theorem. You may add definitions
and helper lemmas to Task.v. Do not modify Task.v.orig. Do not create a
separate solution file. Do not use Admitted, admit, Abort, Axiom, Parameter,
Conjecture, unsafe Rocq flags, or equivalent escape hatches. Compile Task.v
with Rocq and continue fixing errors until it succeeds.

If you fail to produce a compiling Task.v, you must include a short failure
analysis in your final response. Do not stop proof work early merely to
write this report; continue trying until the proof succeeds or you cannot
make further progress. The report should focus on the main capability
bottleneck across the whole attempt. Explain how that
bottleneck prevented completion and state what improved reasoning strategy or tool support
would most likely have changed the outcome."""
    if lr_first:
        prompt += """

Before proving, first carefully design a suitable logical relation. Check
that it supports the required proof obligations and is strong enough to
derive the target theorem.
If an obligation fails, revise the relation instead of patching tactics
locally."""
    if given_r:
        prompt += r"""

Use the following logical relation exactly. Do not replace, weaken, or
strengthen its definition:

Fixpoint R (T : ty) (t : tm) : Prop :=
  <{ empty |-- t \in T }> /\ halts t /\
  (match T with
   | Ty_Bool => True
   | Ty_Arrow T1 T2 =>
       forall t1, R T1 t1 -> R T2 (tm_app t t1)
   end).
"""
    return prompt

def run_agent(problem, workspace, timeout, trace_dir,
              model=None, reasoning_effort=None, lr_first=False,
              given_r=False, local_base_url=None):
    """Run the agent and return the raw result. No formal check."""
    prompt = build_prompt(Path("/workspace/Task.v"), workspace / "card.md",
                          lr_first, given_r)
    codex = shutil.which("codex")
    if not codex:
        raise RuntimeError("codex binary not found")
    codex_cmd = [
        codex, "exec", "--json", "--ephemeral", "--ignore-user-config",
        "--ignore-rules",
        "--skip-git-repo-check", "--sandbox", "workspace-write",
        "--cd", "/workspace",
    ]
    if model:
        codex_cmd += ["--model", model]
    if local_base_url:
        codex_cmd += [
            "--config", 'model_provider="qwen_local"',
            "--config", 'model_providers.qwen_local.name="Qwen local"',
            "--config", f'model_providers.qwen_local.base_url="{local_base_url}"',
            "--config", 'model_providers.qwen_local.wire_api="responses"',
            "--config", "model_providers.qwen_local.requires_openai_auth=false",
            "--config", "model_providers.qwen_local.supports_websockets=false",
        ]
    if reasoning_effort:
        codex_cmd += ["--config", f"model_reasoning_effort={reasoning_effort}"]
    codex_cmd.append("-")
    cmd = isolated_command(workspace, codex_cmd)

    start_time = time.time()
    try:
        env = None
        if local_base_url:
            env = os.environ.copy()
            env["NO_PROXY"] = "127.0.0.1,localhost"
            env["no_proxy"] = env["NO_PROXY"]
        r = subprocess.run(
            cmd, input=prompt, capture_output=True, text=True,
            cwd=workspace, timeout=timeout, env=env,
        )
        elapsed = time.time() - start_time
        _save_trace(trace_dir, problem, r.stdout)
        (trace_dir / f"{problem}.stderr.log").write_text(r.stderr)
        metrics = _parse_result(r.stdout)
        return {"exit": "ok", "elapsed": elapsed, "metrics": metrics,
                "returncode": r.returncode}
    except subprocess.TimeoutExpired as exc:
        elapsed = time.time() - start_time
        partial_stdout = exc.stdout or ""
        if isinstance(partial_stdout, bytes):
            partial_stdout = partial_stdout.decode(errors="replace")
        _save_trace(trace_dir, problem, partial_stdout)
        return {
            "exit": "timeout",
            "elapsed": elapsed,
            "metrics": _empty_metrics(),
            "returncode": None,
        }

def run_agent_retrying_errors(problem, workspace, timeout, trace_dir,
                              model=None, reasoning_effort=None,
                              lr_first=False, given_r=False,
                              local_base_url=None):
    """Retry clean, full-time attempts when Codex exits with an error."""
    attempt = 1
    while True:
        raw = run_agent(
            problem, workspace, timeout, trace_dir,
            model=model, reasoning_effort=reasoning_effort,
            lr_first=lr_first, given_r=given_r,
            local_base_url=local_base_url,
        )
        if raw["exit"] != "ok" or raw.get("returncode", 0) == 0:
            return raw

        _archive_failed_attempt(trace_dir, problem, attempt)
        error_path = trace_dir / f"{problem}.attempt-{attempt}.stderr.log"
        attempt += 1
        print(
            f"Agent error for {problem}; retrying with a fresh "
            f"{timeout}s limit (attempt {attempt}). Error: {error_path}",
            flush=True,
        )
        reset_workspace(workspace)

def check(workspace):
    """Return whether Task.v compiles inside the isolated namespace."""
    rocq = Path.home() / ".opam" / "rocq-dev" / "bin" / "rocq"
    try:
        r = subprocess.run(
            isolated_command(workspace, [str(rocq), "compile", "-q", "Task.v"]),
            capture_output=True, text=True, cwd=workspace, timeout=300,
        )
    except subprocess.TimeoutExpired:
        return False
    return r.returncode == 0

def main():
    install_cleanup_handlers()
    available_benchmarks = sorted(
        path.name
        for path in (ROOT / "benchmarks").iterdir()
        if (path / "card.md").is_file()
        and (path / "input" / "Task.v").is_file()
    )

    parser = argparse.ArgumentParser(description="Run a Rocq benchmark case")
    parser.add_argument(
        "--benchmark", default="stlc", choices=available_benchmarks,
        help="Benchmark case to run (default: stlc)",
    )
    parser.add_argument("--tag", required=True, help="Tag for results/proofs")
    parser.add_argument("--model", help="Codex model; default uses CLI config")
    parser.add_argument("--reasoning-effort")
    parser.add_argument(
        "--local-base-url",
        help="OpenAI-compatible Responses API base URL for a local model",
    )
    parser.add_argument("--lr-first", action="store_true")
    parser.add_argument("--given-r", action="store_true")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--output-root", type=Path, default=OUTPUT_ROOT)
    args = parser.parse_args()

    if args.given_r and args.benchmark != "stlc":
        parser.error("--given-r is only defined for the stlc benchmark")

    benchmark = ROOT / "benchmarks" / args.benchmark
    result_dir = args.output_root / args.benchmark
    results_file = result_dir / f"results_{args.tag}.json"
    proof_dir = result_dir / f"proofs_{args.tag}"
    trace_dir = result_dir / f"traces_{args.tag}"

    previous = load_results(results_file).get(args.benchmark)
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
    if args.local_base_url:
        print(f"Local API: {args.local_base_url}")

    workspace = prepare_workspace(benchmark, args.benchmark)
    task_file = workspace / "Task.v"
    original = (workspace / "Task.v.orig").read_bytes()
    print(f"Isolated workspace: {workspace}")
    try:
        verify_isolation(workspace)
        raw = run_agent_retrying_errors(
            args.benchmark, workspace, args.timeout, trace_dir,
            model=args.model, reasoning_effort=args.reasoning_effort,
            lr_first=args.lr_first,
            given_r=args.given_r,
            local_base_url=args.local_base_url,
        )
        proof_path = proof_dir / f"{args.benchmark}.v"
        if task_file.exists():
            shutil.copy2(task_file, proof_path)
        compiled = check(workspace)
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
            **raw["metrics"],
        }
        results = load_results(results_file)
        results[args.benchmark] = result
        save_results(results, results_file)
        print(
            f"[DONE] {args.benchmark}: {status} "
            f"({int(raw['elapsed'])}s)",
            flush=True,
        )
    finally:
        cleanup_workspace(workspace)


if __name__ == "__main__":
    main()
