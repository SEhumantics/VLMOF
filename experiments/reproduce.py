#!/usr/bin/env python3
"""Run selected evaluation phases into one new evidence directory.

Phases (run in this order when several are selected):
  sources      verify the six pinned OMG downloads offline (fetch them first with `make sources`)
  build        lake build, the timing executable, and the Java bridge (Maven offline)
  correctness  unit/CLI tests, proof clients, authored cases and the EMF comparison fixtures
  public       Train/EMF Compare import and round trips, Train rows of Table 1, full Train DSL
  timing       the nine synthetic workloads of Table 2; must be run alone, never builds

The wrapper downloads nothing: Maven runs with --offline, the Lean toolchain must
already be installed, and public inputs must be supplied as pinned checkouts (see
experiments/cases/fetch-public-cases.sh). OUTPUT must not exist and must lie outside
the repository. Every command, its exit status, logs and tool versions are recorded
in OUTPUT/reproduce.json; SUMMARY.md lists the outcome of each step.
"""

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
from run_public import EMF_COMPARE_REVISION, TRAIN_REVISION  # noqa: E402

PHASES = ("sources", "build", "correctness", "public", "timing")
MAVEN_ARGS = (os.environ.get("MAVEN_ARGS", "") + " --offline").strip()
_LOCAL = re.search(r"-Dmaven\.repo\.local=(\S+)", MAVEN_ARGS)
M2 = Path(_LOCAL[1]) if _LOCAL else Path.home() / ".m2" / "repository"
MAVEN_ARTIFACTS = {  # bridge/pom.xml pins; checked so that offline Maven cannot fail late
    "org.eclipse.emf.ecore 2.39.0": "org/eclipse/emf/org.eclipse.emf.ecore/2.39.0",
    "org.eclipse.emf.ecore.xmi 2.39.0": "org/eclipse/emf/org.eclipse.emf.ecore.xmi/2.39.0",
    "org.eclipse.emf.common 2.42.0": "org/eclipse/emf/org.eclipse.emf.common/2.42.0",
    "jackson-databind 2.18.3": "com/fasterxml/jackson/core/jackson-databind/2.18.3",
    "exec-maven-plugin 3.5.1": "org/codehaus/mojo/exec-maven-plugin/3.5.1",
    "org.eclipse.emf.ecore.xcore 1.28.0": "org/eclipse/emf/org.eclipse.emf.ecore.xcore/1.28.0",
}
BUILD_TOOLS = {"lake", "lean", "mvn", "javac", "leanc", "clang", "ld.lld"}


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def probe(args, cwd=ROOT):
    try:
        done = subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=120)
        return done.returncode, (done.stdout + done.stderr).strip()
    except (OSError, subprocess.TimeoutExpired) as error:
        return None, str(error)


def build_is_current():
    """Problems that would force a build; checked without building anything."""
    problems = []
    code, text = probe(["lake", "build", "--no-build", "VLMOF", "vlmof", "validationBench"])
    if code != 0:
        problems.append("Lean targets are not up to date (run the build phase): " + text[-300:])
    classes = ROOT / "bridge" / "target" / "classes"
    for source in (ROOT / "bridge" / "src" / "main").rglob("*"):
        if not source.is_file():
            continue
        relative = source.relative_to(ROOT / "bridge" / "src" / "main")
        compiled = (classes / relative.relative_to("java")).with_suffix(".class") if source.suffix == ".java" \
            else classes / relative.relative_to("resources")
        if not compiled.is_file() or compiled.stat().st_mtime < source.stat().st_mtime:
            problems.append(f"bridge is not compiled or older than {source.relative_to(ROOT)} (run the build phase)")
            break
    return problems


def prerequisites(args, phases):
    problems = []
    if sys.version_info < (3, 10):
        problems.append("Python 3.10 or newer is required")
    output = args.output.resolve()
    if output.exists():
        problems.append(f"output must not exist: {output}")
    if output == ROOT or ROOT in output.parents:
        problems.append("output must lie outside the repository so evidence cannot be committed by accident")
    if "timing" in phases and len(phases) > 1:
        problems.append("run the timing phase alone, after a separate build, so no build activity overlaps it")
    needs_lean = set(phases) & {"build", "correctness", "public", "timing"}
    needs_java = set(phases) & {"build", "correctness", "public", "timing"}
    if needs_lean:
        toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
        if shutil.which("elan"):
            code, text = probe(["elan", "toolchain", "list"], cwd=Path.home())
            if toolchain not in (text or ""):
                problems.append(f"Lean toolchain {toolchain} is not installed; run `elan toolchain install {toolchain}`")
        elif not shutil.which("lake"):
            problems.append("elan/lake not found; install elan (https://github.com/leanprover/elan)")
    if needs_java:
        code, text = probe(["java", "-version"])
        if code != 0 or not re.search(r'version "21[."]', text):
            problems.append(f"Java 21 is required (found: {text.splitlines()[0] if text else 'none'})")
        code, text = probe(["mvn", "-version"])
        match = re.search(r"Apache Maven (\d+)\.(\d+)", text or "")
        if code != 0 or not match or (int(match[1]), int(match[2])) < (3, 9):
            problems.append("Maven 3.9 or newer is required (MAVEN_ARGS enforces offline mode)")
        wanted = dict(MAVEN_ARTIFACTS)
        if "public" not in phases:
            wanted.pop("org.eclipse.emf.ecore.xcore 1.28.0")
        missing = [name for name, path in wanted.items() if not any((M2 / path).glob("*.jar"))]
        if missing:
            problems.append("Maven dependencies are not in the local repository " + str(M2) + ": "
                            + ", ".join(missing) + ". Resolve them once, with network access, by running "
                            "`mvn -f bridge/pom.xml test-compile dependency:tree` (see REPRODUCING.md).")
    if "public" in phases:
        for label, path, revision in (("--train", args.train, TRAIN_REVISION),
                                      ("--emf-compare", args.emf_compare, EMF_COMPARE_REVISION)):
            if path is None:
                problems.append(f"the public phase needs {label} (a checkout made by fetch-public-cases.sh)")
                continue
            code, text = probe(["git", "rev-parse", "HEAD"], cwd=path) if path.is_dir() else (None, "missing")
            if text != revision:
                problems.append(f"{label} {path} is not a checkout of {revision} (found: {text})")
    if set(phases) & {"correctness", "public", "timing"} and "build" not in phases and needs_lean:
        problems.extend(build_is_current())
    return problems


def running_build_tools():
    names = []
    for status in Path("/proc").glob("[0-9]*/comm"):
        try:
            name = status.read_text().strip()
        except OSError:
            continue
        if name in BUILD_TOOLS:
            names.append(name)
    return sorted(names)


class Run:
    def __init__(self, output: Path, report: dict):
        self.output, self.report, self.sequence = output, report, 0
        (output / "logs").mkdir(parents=True)

    def save(self):
        temporary = self.output / "reproduce.json.tmp"
        temporary.write_text(json.dumps(self.report, indent=2) + "\n", encoding="utf-8")
        temporary.replace(self.output / "reproduce.json")

    def step(self, phase, label, status, **extra):
        record = {"phase": phase, "label": label, "status": status, **extra}
        self.report["steps"].append(record)
        self.save()
        print(f"[{phase}] {label}: {status}", flush=True)
        return record

    def command(self, phase, label, args, ok=(0,), env=None, timeout=None):
        self.sequence += 1
        stem = self.output / "logs" / f"{self.sequence:03d}-{label}"
        argv = [str(a) for a in args]
        start, begin = utc(), time.perf_counter()
        error, code = None, None
        with open(f"{stem}.stdout", "wb") as out, open(f"{stem}.stderr", "wb") as err:
            try:
                code = subprocess.run(argv, cwd=ROOT, stdout=out, stderr=err, timeout=timeout,
                                      env={**os.environ, **self.report["environment_overrides"], **(env or {})}).returncode
            except (OSError, subprocess.TimeoutExpired) as failure:
                error = f"{type(failure).__name__}: {failure}"
        logs = {kind: {"path": f"logs/{stem.name}.{kind}", "bytes": Path(f"{stem}.{kind}").stat().st_size,
                       "sha256": sha256(Path(f"{stem}.{kind}"))} for kind in ("stdout", "stderr")}
        status = "passed" if code in ok and error is None else "failed"
        return self.step(phase, label, status, command=argv, env=env or {}, started_utc=start,
                         duration_seconds=round(time.perf_counter() - begin, 3), exit=code, error=error, logs=logs)

    def text(self, record, kind="stdout"):
        return (self.output / record["logs"][kind]["path"]).read_text(encoding="utf-8", errors="replace")


def environment(run: Run):
    for label, args in (("python-version", [sys.executable, "--version"]), ("git-version", ["git", "--version"]),
                        ("git-commit", ["git", "rev-parse", "HEAD"]),
                        ("git-status", ["git", "status", "--porcelain=v1", "--untracked-files=all"]),
                        ("elan-version", ["elan", "--version"]), ("lake-version", ["lake", "--version"]),
                        ("lean-version", ["lake", "env", "lean", "--version"]), ("java-version", ["java", "-version"]),
                        ("maven-version", ["mvn", "-version"])):
        run.command("environment", label, args, ok=(0, None))
    cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                if line.startswith("model name")), None) if Path("/proc/cpuinfo").exists() else None
    memory = next((line.split(":", 1)[1].strip() for line in Path("/proc/meminfo").read_text().splitlines()
                   if line.startswith("MemTotal")), None) if Path("/proc/meminfo").exists() else None
    run.report["machine"] = {"system": platform.system(), "release": platform.release(), "machine": platform.machine(),
                             "cpu": cpu, "logical_cpus": os.cpu_count(), "memory": memory,
                             "load_average_at_start": os.getloadavg()}
    run.save()


def sources(run: Run):
    run.command("sources", "verify-omg-sources", [sys.executable, "scripts/sources.py", "verify"])


def build(run: Run):
    run.command("build", "lake-build", ["lake", "build"])
    run.command("build", "lake-build-validationBench", ["lake", "build", "validationBench"])
    run.command("build", "bridge-test-compile", ["mvn", "-q", "-f", "bridge/pom.xml", "test-compile"])


def table1(run: Run, phase, results):
    present = [path for path in results if path.is_file()]
    if not present:
        return run.step(phase, "table1-summary", "not-run", reason="no EMF comparison results")
    json_path = run.output / phase / "table1.json"
    return run.command(phase, "table1-summary", [sys.executable, "experiments/evidence.py", "table1",
                                                 *present, "--json", json_path])


def correctness(run: Run):
    out = run.output / "correctness"
    out.mkdir()
    run.command("correctness", "python-unit-tests", [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"])
    run.command("correctness", "proof-client-axioms", ["lake", "env", "lean", "experiments/ProofClient.lean"])
    run.command("correctness", "paper-map-lean", ["lake", "env", "lean", "experiments/PaperMap.lean"])
    run.command("correctness", "cli-tests", [sys.executable, "scripts/test_cli.py", "-v"])
    run.command("correctness", "authored-cli-cases", [sys.executable, "experiments/run.py", "--output", out / "authored-cli"])
    run.command("correctness", "emf-comparison", [sys.executable, "experiments/run_emf_validation.py",
                                                  "--output", out / "emf-comparison"])
    table1(run, "correctness", [out / "emf-comparison" / "results.json"])


def train_fixture(path: Path, ident, condition, ecore, xmi, expected, obligation):
    path.write_text(json.dumps({
        "id": ident, "condition": condition, "ecore": [str(ecore)], "xmi": [str(xmi)],
        "obligation": obligation,
        "state_relation": "EMF loaded observations compared with the E1 Core state under native identity correspondence.",
        "expected": expected, "timing_eligible": False}, indent=2) + "\n", encoding="utf-8")


def public(run: Run, train: Path, emf_compare: Path):
    out = run.output / "public"
    out.mkdir()
    inventory = out / "train-snapshot-inventory.json"
    record = run.command("public", "train-snapshot-inventory",
                         [sys.executable, "experiments/cases/inventory_train_snapshots.py", train, inventory])
    if record["status"] == "passed":
        same = inventory.read_bytes() == (ROOT / "experiments/cases/train-snapshot-inventory.json").read_bytes()
        run.step("public", "inventory-matches-committed", "passed" if same else "failed",
                 compared=["public/train-snapshot-inventory.json", "experiments/cases/train-snapshot-inventory.json"])
    runner = out / "public-runner"
    run.command("public", "public-runner", [sys.executable, "experiments/run_public.py", "--train", train,
                                            "--emf-compare", emf_compare, "--output", runner],
                env={"CHECKER": str(ROOT / ".lake/build/bin/vlmof")})
    profile, adapted = runner / "artifacts/railway.profile.ecore", runner / "cases/railway-batch-1/adapted.xmi"
    comparison = out / "train-emf-comparison"
    if profile.is_file() and adapted.is_file():
        companion = {item["name"]: {k["path"]: k["sha256"] for k in item["key_files"]} for item in
                     json.loads((ROOT / "experiments/companion-evidence.json").read_text())["collections"]}
        historical = companion["third-review-public"]
        same = {"railway.profile.ecore": sha256(profile) == historical["artifacts/railway.profile.ecore"],
                "adapted.xmi": sha256(adapted) == historical["cases/railway-batch-1/adapted.xmi"]}
        run.step("public", "adapted-inputs-match-retained", "passed" if all(same.values()) else "differs",
                 identical_to_retained_bytes=same)
        fixtures = out / "train-fixtures"
        fixtures.mkdir()
        train_fixture(fixtures / "train-batch-1-profile.fixture.json", "train-batch-1-profile",
                      "public Train v1.0 profile adaptation with materialized enum defaults (fresh run_public.py output)",
                      Path("../public-runner/artifacts/railway.profile.ecore"),
                      Path("../public-runner/cases/railway-batch-1/adapted.xmi"), {},
                      "Table 1 row 'Train with explicit defaults': decisions and loaded-state comparison.")
        train_fixture(fixtures / "public-train-raw-batch-1-profile.fixture.json", "public-train-raw-batch-1-profile",
                      "pinned Train profile schema with untouched public XMI",
                      Path("../public-runner/artifacts/railway.profile.ecore"),
                      (train / "models/railway-batch-1.xmi").resolve(), {"emf": "accepted", "vlmof": "accepted"},
                      "Table 1 row 'Train with original omissions': decisions and loaded-state comparison.")
        run.command("public", "train-emf-comparison", [
            sys.executable, "experiments/run_emf_validation.py", "--output", comparison,
            "--fixture", fixtures / "train-batch-1-profile.fixture.json",
            "--fixture", fixtures / "public-train-raw-batch-1-profile.fixture.json"])
    else:
        run.step("public", "train-emf-comparison", "not-run", reason="public runner produced no adapted Train inputs")
    core = comparison / "normalized/public-train-raw-batch-1-profile.e1.json"
    if core.is_file():
        rendered = out / "full-v1-batch-1.dsl"
        record = run.command("public", "render-full-train-dsl",
                             [sys.executable, "scripts/train_walkthrough.py", core, rendered])
        if record["status"] == "passed":
            same = rendered.read_bytes() == (ROOT / "examples/train/full-v1-batch-1.dsl").read_bytes()
            run.step("public", "full-train-dsl-matches-committed", "passed" if same else "failed")
        run.command("public", "full-train-walkthrough", ["lake", "env", "lean", "--run", "experiments/TrainWalkthrough.lean",
                                                         core, "examples/train/full-v1-batch-1.dsl"])
    else:
        run.step("public", "full-train-walkthrough", "not-run", reason="no normalized original-omissions Train document")
    table1(run, "public", [comparison / "results.json"])


def timing(run: Run, args):
    out = run.output / "timing"
    out.mkdir()
    run.report["timing_quiescence"] = {"load_average_before": os.getloadavg(),
                                       "build_tool_processes_before": running_build_tools()}
    if run.report["timing_quiescence"]["build_tool_processes_before"]:
        print("warning: build-tool processes are running: "
              + ", ".join(run.report["timing_quiescence"]["build_tool_processes_before"]), flush=True)
    policy = ["--trials", args.trials, "--warmups", args.warmups, "--repetitions", args.repetitions]
    record = run.command("timing", "multifamily-timing", [sys.executable, "experiments/run_fifth_evaluation.py",
                                                          "--output", out / "multifamily", *policy], ok=(0, 1))
    # Exit 1 also reports incomplete trials, which the protocol expects (deep chain timeouts).
    if record["exit"] == 1:
        record["note"] = "exit 1: at least one trial incomplete or failed; see table2-summary"
    run.report["timing_quiescence"].update(load_average_after=os.getloadavg(),
                                           build_tool_processes_after=running_build_tools())
    run.save()
    if (out / "multifamily" / "results.json").is_file() and \
            json.loads((out / "multifamily" / "results.json").read_text()).get("trials"):
        run.command("timing", "table2-summary", [sys.executable, "experiments/evidence.py", "table2",
                                                 out / "multifamily", "--json", out / "table2.json"])
    else:
        run.step("timing", "table2-summary", "not-run", reason="no timing trials were recorded")


def summary(run: Run):
    lines = ["# Reproduction run", "", f"Repository: `{ROOT}`", f"Phases: {', '.join(run.report['phases'])}",
             f"Started: {run.report['started_utc']}  Finished: {run.report['finished_utc']}", "",
             "| Phase | Step | Status | Exit | Seconds | Log |", "|---|---|---|---|---|---|"]
    for step in run.report["steps"]:
        log = step.get("logs", {}).get("stdout", {}).get("path", "")
        lines.append(f"| {step['phase']} | {step['label']} | {step['status']} | {step.get('exit', '')} | "
                     f"{step.get('duration_seconds', '')} | {log} |")
    lines += ["", "Statuses: passed, failed, differs (bytes differ from retained evidence), not-run "
              "(a prerequisite step produced no input). Details and hashes are in reproduce.json.", ""]
    (run.output / "SUMMARY.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", required=True, type=Path, help="new directory outside the repository")
    parser.add_argument("--phase", action="append", choices=PHASES, required=True, help="repeat to select several")
    parser.add_argument("--train", type=Path, help="Train Benchmark checkout at the pinned revision (public phase)")
    parser.add_argument("--emf-compare", type=Path, help="EMF Compare checkout at the pinned revision (public phase)")
    parser.add_argument("--trials", type=int, default=5, help="timing: process trials per cell (paper: 5)")
    parser.add_argument("--warmups", type=int, default=10, help="timing: warmups per process (paper: 10)")
    parser.add_argument("--repetitions", type=int, default=30, help="timing: retained repetitions (paper: 30)")
    parser.add_argument("--check-only", action="store_true", help="check prerequisites, create nothing")
    args = parser.parse_args()
    phases = [phase for phase in PHASES if phase in args.phase]
    args.train = args.train.resolve() if args.train else None
    args.emf_compare = args.emf_compare.resolve() if args.emf_compare else None
    problems = prerequisites(args, phases)
    for problem in problems:
        print(f"prerequisite: {problem}", file=sys.stderr)
    if problems or args.check_only:
        if not problems:
            print("prerequisites satisfied for: " + ", ".join(phases))
        return 2 if problems else 0
    output = args.output.resolve()
    output.mkdir(parents=True)
    protocol = (args.trials, args.warmups, args.repetitions) == (5, 10, 30)
    report = {"format": "vlmof-reproduce-1", "repository": str(ROOT), "invocation": sys.argv, "phases": phases,
              "started_utc": utc(), "environment_overrides": {"MAVEN_ARGS": MAVEN_ARGS},
              "public_inputs": {"train": str(args.train) if args.train else None,
                                "emf_compare": str(args.emf_compare) if args.emf_compare else None},
              "timing_policy": {"trials": args.trials, "warmups": args.warmups, "repetitions": args.repetitions,
                                "paper_protocol": protocol} if "timing" in phases else None,
              "steps": []}
    run = Run(output, report)
    environment(run)
    for phase in phases:
        if phase == "public":
            public(run, args.train, args.emf_compare)
        elif phase == "timing":
            timing(run, args)
        else:
            {"sources": sources, "build": build, "correctness": correctness}[phase](run)
    report["finished_utc"] = utc()
    failed = [s["label"] for s in report["steps"] if s["phase"] != "environment" and s["status"] != "passed"]
    report["all_steps_passed"] = not failed
    run.save()
    summary(run)
    print(f"{len(report['steps'])} steps; not passed: {failed or 'none'}; see {output / 'SUMMARY.md'}")
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main())
