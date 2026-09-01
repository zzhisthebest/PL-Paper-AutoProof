#!/usr/bin/env python3
"""Run Codex on a Rocq benchmark case.

Usage:
    python scripts/test.py --benchmark stlc --tag codex
    python scripts/test.py --benchmark systemf --tag codex \
        --model MODEL --reasoning-effort high
"""

import argparse, json, subprocess, sys, time, shutil, os, signal, atexit
from pathlib import Path

ROOT = Path("/data0/zzh/PL-Paper-AutoProof")
OUTPUT_ROOT = Path("/data0/zzh/benchmarkResults")
PERMISSION_SNAPSHOT_FILE = ROOT / ".test_permission_snapshot.json"

_PERMISSION_SNAPSHOT = {}
_EXITING_AFTER_SIGNAL = False

def _save_trace(trace_dir, problem, raw_stdout):
    trace_dir.mkdir(parents=True, exist_ok=True)
    (trace_dir / f"{problem}.jsonl").write_text(raw_stdout)

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

def ensure_orig(task_path):
    orig_path = task_path.with_suffix(".v.orig")
    if not orig_path.exists():
        shutil.copy2(task_path, orig_path)

def restore_from_orig(task_path):
    orig_path = task_path.with_suffix(".v.orig")
    if orig_path.exists():
        shutil.copy2(orig_path, task_path)

def remove_build_artifacts(task_path):
    """Remove stale Rocq outputs that could reveal an earlier solution."""
    artifacts = [
        task_path.with_suffix(".vo"),
        task_path.with_suffix(".vos"),
        task_path.with_suffix(".vok"),
        task_path.with_suffix(".glob"),
        task_path.parent / f".{task_path.stem}.aux",
    ]
    for artifact in artifacts:
        artifact.unlink(missing_ok=True)

def _remember_mode(path):
    if path not in _PERMISSION_SNAPSHOT:
        _PERMISSION_SNAPSHOT[path] = path.stat().st_mode & 0o777
        PERMISSION_SNAPSHOT_FILE.parent.mkdir(parents=True, exist_ok=True)
        PERMISSION_SNAPSHOT_FILE.write_text(json.dumps(
            {str(p): mode for p, mode in _PERMISSION_SNAPSHOT.items()},
            indent=2
        ) + "\n")

def _chmod_recorded(path, mode):
    if not path.exists():
        return
    try:
        _remember_mode(path)
        path.chmod(mode)
    except FileNotFoundError:
        pass

def _hide_path(path):
    """Make a path unreadable during evaluation."""
    if not path.exists() or path.is_symlink():
        return
    _chmod_recorded(path, 0o000)

def restore_hidden_path_permissions():
    """Restore permissions changed by _hide_path."""
    snapshot = dict(_PERMISSION_SNAPSHOT)
    if PERMISSION_SNAPSHOT_FILE.exists():
        try:
            snapshot.update({
                Path(path): mode
                for path, mode in json.loads(PERMISSION_SNAPSHOT_FILE.read_text()).items()
            })
        except json.JSONDecodeError:
            pass
    for path, mode in sorted(snapshot.items(), key=lambda item: len(item[0].parts)):
        try:
            path.chmod(mode)
        except FileNotFoundError:
            pass
    _PERMISSION_SNAPSHOT.clear()
    try:
        PERMISSION_SNAPSHOT_FILE.unlink(missing_ok=True)
    except PermissionError:
        pass

def _restore_and_exit_on_signal(signum, frame):
    """Restore permissions immediately on Ctrl+C/SIGTERM."""
    global _EXITING_AFTER_SIGNAL
    if _EXITING_AFTER_SIGNAL:
        os._exit(128 + signum)
    _EXITING_AFTER_SIGNAL = True
    print("\nInterrupted; restoring file permissions...", file=sys.stderr, flush=True)
    try:
        restore_hidden_path_permissions()
    except Exception as exc:
        print(f"Warning: failed to restore permissions: {exc}", file=sys.stderr, flush=True)
    os._exit(128 + signum)

def install_exit_handlers():
    atexit.register(restore_hidden_path_permissions)
    signal.signal(signal.SIGINT, _restore_and_exit_on_signal)
    signal.signal(signal.SIGTERM, _restore_and_exit_on_signal)

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
with Rocq and continue fixing errors until it succeeds."""
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

def run_agent(task_path, card_path, timeout, trace_dir,
              model=None, reasoning_effort=None, lr_first=False,
              given_r=False):
    """Run the agent and return the raw result. No formal check."""
    problem = task_path.parent.parent.name
    prompt = build_prompt(task_path, card_path, lr_first, given_r)
    cmd = [
        "codex", "exec", "--json", "--ephemeral", "--ignore-rules",
        "--skip-git-repo-check", "--sandbox", "workspace-write",
        "--cd", str(task_path.parent),
    ]
    if model:
        cmd += ["--model", model]
    if reasoning_effort:
        cmd += ["--config", f"model_reasoning_effort={reasoning_effort}"]
    cmd.append("-")

    start_time = time.time()
    try:
        r = subprocess.run(
            cmd, input=prompt, capture_output=True, text=True,
            cwd=task_path.parent, timeout=timeout,
        )
        elapsed = time.time() - start_time
        _save_trace(trace_dir, problem, r.stdout)
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

def check(task_path):
    """Return whether Task.v compiles with Rocq."""
    try:
        r = subprocess.run(
            ["rocq", "compile", "-q", task_path.name],
            capture_output=True, text=True, cwd=task_path.parent, timeout=300,
        )
    except subprocess.TimeoutExpired:
        return False
    return r.returncode == 0

def main():
    install_exit_handlers()
    restore_hidden_path_permissions()

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
    parser.add_argument("--lr-first", action="store_true")
    parser.add_argument("--given-r", action="store_true")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--output-root", type=Path, default=OUTPUT_ROOT)
    args = parser.parse_args()

    if args.given_r and args.benchmark != "stlc":
        parser.error("--given-r is only defined for the stlc benchmark")

    benchmark = ROOT / "benchmarks" / args.benchmark
    task_file = benchmark / "input" / "Task.v"
    card_file = benchmark / "card.md"

    result_dir = args.output_root / args.benchmark
    results_file = result_dir / f"results_{args.tag}.json"
    proof_dir = result_dir / f"proofs_{args.tag}"
    trace_dir = result_dir / f"traces_{args.tag}"
    result_dir.mkdir(parents=True, exist_ok=True)
    proof_dir.mkdir(parents=True, exist_ok=True)
    trace_dir.mkdir(parents=True, exist_ok=True)

    ensure_orig(task_file)
    restore_from_orig(task_file)
    remove_build_artifacts(task_file)

    print(f"Case:    {args.benchmark}")
    print(f"Task:    {task_file}")
    print(f"Results: {results_file}")
    print(f"Proofs:  {proof_dir}/")
    print(f"Traces:  {trace_dir}/")

    try:
        _hide_path(ROOT / "theories")
        raw = run_agent(
            task_file, card_file, args.timeout, trace_dir,
            model=args.model, reasoning_effort=args.reasoning_effort,
            lr_first=args.lr_first,
            given_r=args.given_r,
        )
        proof_path = proof_dir / f"{args.benchmark}.v"
        if task_file.exists():
            shutil.copy2(task_file, proof_path)
        compiled = check(task_file)

        if raw["exit"] == "timeout":
            status = "timeout"
        elif raw["returncode"] != 0:
            status = "agent_error"
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
    finally:
        restore_from_orig(task_file)
        remove_build_artifacts(task_file)
        restore_hidden_path_permissions()


if __name__ == "__main__":
    main()
