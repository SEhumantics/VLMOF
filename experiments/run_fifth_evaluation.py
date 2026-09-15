#!/usr/bin/env python3
"""Run correctness, then counterbalanced independent-process timing trials."""

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "experiments" / "run_emf_validation.py"
CASES = ROOT / "experiments" / "cases" / "emf-validation"


def output_text(value):
    if value is None:
        return ""
    return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, timeout=1800):
    start = time.perf_counter_ns()
    invocation = [str(x) for x in command]
    try:
        result = subprocess.run(invocation, cwd=ROOT, text=True,
                                capture_output=True, timeout=timeout)
        return {"command": invocation, "exit": result.returncode, "timed_out": False,
                "wall_nanoseconds": time.perf_counter_ns() - start,
                "stdout": result.stdout, "stderr": result.stderr}
    except subprocess.TimeoutExpired as error:
        return {"command": invocation, "exit": None, "timed_out": True,
                "wall_nanoseconds": time.perf_counter_ns() - start,
                "stdout": output_text(error.stdout), "stderr": output_text(error.stderr)}


def timing_schedule(cells, trials):
    """Return traversal and tool order while preserving each cell's stable parity."""
    scheduled = []
    for trial in range(1, trials + 1):
        ordered = cells if trial % 2 else list(reversed(cells))
        for cell in ordered:
            stable_cell_index = cells.index(cell)
            emf_first = ((stable_cell_index + trial) % 2 == 1)
            scheduled.append((trial, cell, "emf-first" if emf_first else "vlmof-first"))
    return scheduled


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--trials", default=5, type=int)
    parser.add_argument("--warmups", default=10, type=int)
    parser.add_argument("--repetitions", default=30, type=int)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists(): raise SystemExit(f"output must not exist: {output}")
    output.mkdir(parents=True)

    subprocess.run([sys.executable, ROOT / "experiments" / "generate_scaling_cases.py"],
                   cwd=ROOT, check=True)
    cells = []
    for family, sizes in (("containment-inheritance", (11, 101, 501)),
                          ("train-projection", (10, 100, 500)),
                          ("recursive-containment", (11, 101, 501))):
        for size in sizes:
            cells.append((family, size, CASES / f"{family}-{size}.fixture.json"))

    report = {"format": "vlmof-fifth-evaluation-1", "created_utc": datetime.now(timezone.utc).isoformat(),
              "environment": {"platform": platform.platform(), "python": sys.version},
              "policy": {"trials": args.trials, "warmups": args.warmups,
                         "repetitions": args.repetitions, "counterbalanced": True},
              "inputs": {str(p): sha(p) for _, _, p in cells}, "correctness": [], "trials": []}

    correctness_dir = output / "correctness"
    command = [sys.executable, BASE, "--output", correctness_dir]
    correct = run(command)
    (output / "correctness.stdout").write_text(correct.pop("stdout"), encoding="utf-8")
    (output / "correctness.stderr").write_text(correct.pop("stderr"), encoding="utf-8")
    report["correctness"].append(correct)
    if correct["exit"] != 0:
        (output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        return correct["exit"]

    for trial, (family, size, fixture), tool_order in timing_schedule(cells, args.trials):
            emf_first = tool_order == "emf-first"
            # The base runner records separate JVM and Lean processes. A small
            # runner option controls their order without changing either worker.
            trial_dir = output / "timing" / f"trial-{trial}" / f"{family}-{size}"
            cmd = [sys.executable, BASE, "--output", trial_dir, "--fixture", fixture,
                   "--measure", "--warmups", args.warmups, "--repetitions", args.repetitions,
                   "--timing-order", "emf-first" if emf_first else "vlmof-first"]
            result = run(cmd)
            stdout, stderr = result.pop("stdout"), result.pop("stderr")
            trial_dir.parent.mkdir(parents=True, exist_ok=True)
            (trial_dir.parent / f"{family}-{size}.launcher.stdout").write_text(stdout, encoding="utf-8")
            (trial_dir.parent / f"{family}-{size}.launcher.stderr").write_text(stderr, encoding="utf-8")
            worker_result = trial_dir / "results.json"
            worker_summary = None
            if worker_result.is_file():
                worker_data = json.loads(worker_result.read_text(encoding="utf-8"))
                rows = worker_data.get("fixtures", [])
                worker_summary = {"path": str(worker_result.relative_to(output)),
                                  "sha256": sha(worker_result),
                                  "all_expected": worker_data.get("all_expected"),
                                  "timing_complete": rows[0].get("timing", {}).get("complete") if len(rows) == 1 else False}
            report["trials"].append({"trial": trial, "family": family, "size": size,
                                     "order": tool_order, "worker": worker_summary, **result})
            (output / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return 0 if all(x["exit"] == 0 for x in report["trials"]) else 1


if __name__ == "__main__": raise SystemExit(main())
