#!/usr/bin/env python3
"""Run the declared actual-EMF structural validation protocol into a new directory.

This runner records correctness by default.  Pass --measure only after the
integrator has declared builds quiescent: it then runs the protocol's preloaded
positive timing condition (10 warmups and 30 retained repetitions by default).
It never retries, repairs, or overwrites an existing evidence directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FIXTURES = ROOT / "experiments" / "cases" / "emf-validation"
BRIDGE_POM = ROOT / "bridge" / "pom.xml"
HARNESS = "org.vlmof.bridge.EmfValidationHarness"
INTERCHANGE = "org.vlmof.bridge.EmfInterchange"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(name, args, output: Path, cwd=ROOT, timeout=120):
    start = time.perf_counter_ns()
    try:
        completed = subprocess.run(args, cwd=cwd, text=True, capture_output=True, timeout=timeout)
        result = {"name": name, "command": [str(arg) for arg in args], "cwd": str(cwd),
                  "exit": completed.returncode, "elapsed_nanoseconds": time.perf_counter_ns() - start}
        stdout, stderr = completed.stdout, completed.stderr
    except (OSError, subprocess.TimeoutExpired) as error:
        result = {"name": name, "command": [str(arg) for arg in args], "cwd": str(cwd),
                  "exit": None, "error": str(error), "elapsed_nanoseconds": time.perf_counter_ns() - start}
        stdout, stderr = "", str(error)
    stem = f"{len(list((output / 'commands').glob('*'))):03d}-{name}"
    stdout_path = output / "commands" / f"{stem}.stdout"
    stderr_path = output / "commands" / f"{stem}.stderr"
    stdout_path.write_text(stdout, encoding="utf-8")
    stderr_path.write_text(stderr, encoding="utf-8")
    result["stdout"] = {"path": str(stdout_path.relative_to(output)), "sha256": digest(stdout_path)}
    result["stderr"] = {"path": str(stderr_path.relative_to(output)), "sha256": digest(stderr_path)}
    return result, stdout


def json_output(record, stdout, semantic_exits=(0,)):
    if record.get("exit") not in semantic_exits:
        return None
    try:
        return json.loads(stdout)
    except json.JSONDecodeError:
        return None


def lean_status(record, report):
    """Keep VL-MOF's documented semantic, malformed, and unsupported exits distinct."""
    if report is None:
        return "execution-failure"
    if record.get("exit") in (0, 1):
        return "accepted" if report.get("status") == "accepted" else "rejected"
    if record.get("exit") == 2 and report.get("status") in ("malformed", "parse-malformed"):
        return "malformed"
    if record.get("exit") == 3 and report.get("status") == "unsupported":
        return "unsupported"
    return "execution-failure"


def phase_status(report, accepted_key="accepted"):
    if report is None:
        return "execution-failure"
    if report.get("status") == "execution-failure":
        return "execution-failure"
    return "accepted" if report.get(accepted_key) is True else "rejected"


def fixture_paths(manifest_path: Path, fixture):
    paths = []
    for field in ("ecore", "xmi"):
        for value in fixture[field]:
            path = (manifest_path.parent / value).resolve()
            paths.append(path)
    return paths


def bridge_command(main_class, args):
    return ["mvn", "-q", "-f", str(BRIDGE_POM), "exec:java",
            f"-Dexec.mainClass={main_class}", f"-Dexec.args={' '.join(str(arg) for arg in args)}"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--fixture", action="append", type=Path,
                        help="Fixture manifest; defaults to every local *.fixture.json.")
    parser.add_argument("--measure", action="store_true", help="Run approved positive timing condition.")
    parser.add_argument("--warmups", default=10, type=int)
    parser.add_argument("--repetitions", default=30, type=int)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise SystemExit(f"output directory must not exist: {output}")
    if args.warmups < 0 or args.repetitions <= 0:
        raise SystemExit("warmups must be nonnegative and repetitions positive")
    output.mkdir(parents=True)
    (output / "commands").mkdir()
    (output / "normalized").mkdir()

    manifest_paths = [path.resolve() for path in args.fixture] if args.fixture else sorted(DEFAULT_FIXTURES.glob("*.fixture.json"))
    if not manifest_paths:
        raise SystemExit("no fixture manifests selected")
    report = {
        "protocol": "emof-emf-validation-1",
        "scope": "Actual EMF Ecore/EObject validation plus lossless E1 normalization observation.",
        "measurement_requested": args.measure,
        "timing_policy": {"warmups": args.warmups, "repetitions": args.repetitions,
                          "boundary": "preloaded-schema-and-instance-validation"},
        "environment": {"platform": platform.platform(), "python": sys.version,
                        "cwd": str(ROOT), "pid": os.getpid()},
        "repository": {}, "fixtures": []}
    for key, cmd in {"commit": ["git", "rev-parse", "HEAD"], "dirty": ["git", "status", "--porcelain"]}.items():
        row, stdout = command(f"git-{key}", cmd, output)
        report["repository"][key] = {"record": row, "value": stdout.strip()}
    report["tooling"] = {}
    for key, cmd in {
            "java-version": ["java", "-version"],
            "maven-version": ["mvn", "--version"],
            "maven-dependency-tree": ["mvn", "-f", str(BRIDGE_POM), "dependency:tree"],
    }.items():
        row, _ = command(key, cmd, output)
        report["tooling"][key] = row
    hash_paths = {
        "bridge_pom": BRIDGE_POM,
        "emf_validation_harness": ROOT / "bridge" / "src" / "main" / "java" / "org" / "vlmof" / "bridge" / "EmfValidationHarness.java",
        "runner": Path(__file__),
        "vlmof_binary": ROOT / ".lake" / "build" / "bin" / "vlmof",
        "validation_bench_binary": ROOT / ".lake" / "build" / "bin" / "validationBench",
        "ecore_2_39_jar": Path.home() / ".m2" / "repository" / "org" / "eclipse" / "emf" / "org.eclipse.emf.ecore" / "2.39.0" / "org.eclipse.emf.ecore-2.39.0.jar",
        "ecore_2_39_sources": Path.home() / ".m2" / "repository" / "org" / "eclipse" / "emf" / "org.eclipse.emf.ecore" / "2.39.0" / "org.eclipse.emf.ecore-2.39.0-sources.jar",
    }
    report["artifact_hashes"] = {name: digest(path) if path.is_file() else None for name, path in hash_paths.items()}

    source_before = {}
    for manifest_path in manifest_paths:
        fixture = json.loads(manifest_path.read_text(encoding="utf-8"))
        if not isinstance(fixture.get("ecore"), list) or not isinstance(fixture.get("xmi"), list):
            raise SystemExit(f"invalid fixture manifest: {manifest_path}")
        inputs = [manifest_path, *fixture_paths(manifest_path, fixture)]
        source_before.update({str(path): digest(path) for path in inputs})
        fixture_row = {"id": fixture.get("id"), "manifest": str(manifest_path),
                       "condition": fixture.get("condition"), "obligation": fixture.get("obligation"),
                       "state_relation": fixture.get("state_relation"), "expected": fixture.get("expected", {}),
                       "source_hashes": {str(path): source_before[str(path)] for path in inputs},
                       "phases": {}, "matches_expected": None}

        emf_record, emf_stdout = command(f"{fixture_row['id']}-emf-validate",
                                          bridge_command(HARNESS, ["validate", manifest_path]), output)
        emf_report = json_output(emf_record, emf_stdout)
        emf_status = phase_status(emf_report)
        fixture_row["phases"]["emf_validation"] = {"status": emf_status, "record": emf_record,
                                                     "report": emf_report}

        core = output / "normalized" / f"{fixture_row['id']}.e1.json"
        source_args = ["import", *[(manifest_path.parent / path).resolve() for path in fixture["ecore"]], "--",
                       *[(manifest_path.parent / path).resolve() for path in fixture["xmi"]]]
        normalization_record, normalization_stdout = command(
            f"{fixture_row['id']}-normalize", bridge_command(INTERCHANGE, source_args), output)
        normalization_json = json_output(normalization_record, normalization_stdout)
        if normalization_json is not None:
            core.write_text(json.dumps(normalization_json, indent=2) + "\n", encoding="utf-8")
            fixture_row["phases"]["normalization"] = {"status": "accepted", "record": normalization_record,
                                                        "core": str(core.relative_to(output)), "sha256": digest(core)}
            checker = ROOT / ".lake" / "build" / "bin" / "vlmof"
            if checker.exists():
                lean_record, lean_stdout = command(f"{fixture_row['id']}-vlmof-validate",
                                                    [str(checker), "check-json", str(core)], output)
                # `vlmof` uses exit 1 for a validly decoded semantic rejection.
                try:
                    lean_report = json.loads(lean_stdout)
                except json.JSONDecodeError:
                    lean_report = None
                fixture_row["phases"]["vlmof_validation"] = {
                    "status": lean_status(lean_record, lean_report),
                    "record": lean_record, "report": lean_report}
            else:
                fixture_row["phases"]["vlmof_validation"] = {"status": "not-run",
                    "reason": "Build .lake/build/bin/vlmof before protocol execution."}
        else:
            fixture_row["phases"]["normalization"] = {"status": "execution-failure", "record": normalization_record}
            fixture_row["phases"]["vlmof_validation"] = {"status": "not-run", "reason": "normalization failed"}

        expected = fixture_row["expected"]
        if expected:
            observed = {"emf": fixture_row["phases"]["emf_validation"]["status"],
                        "vlmof": fixture_row["phases"]["vlmof_validation"]["status"]}
            fixture_row["matches_expected"] = all(observed.get(key) == value for key, value in expected.items())
        if args.measure and fixture.get("timing_eligible") and emf_status == "accepted" and \
                fixture_row["phases"]["vlmof_validation"]["status"] == "accepted":
            emf_timing, emf_timing_stdout = command(f"{fixture_row['id']}-emf-warm",
                bridge_command(HARNESS, ["warm-validate", manifest_path, args.warmups, args.repetitions]), output)
            lean_timing, lean_timing_stdout = command(f"{fixture_row['id']}-lean-warm",
                [str(ROOT / ".lake" / "build" / "bin" / "validationBench"), str(core), str(args.warmups), str(args.repetitions)], output)
            fixture_row["timing"] = {"emf": {"record": emf_timing, "report": json_output(emf_timing, emf_timing_stdout)},
                                      "lean": {"record": lean_timing, "report": json_output(lean_timing, lean_timing_stdout)}}
        report["fixtures"].append(fixture_row)

    source_after = {path: digest(Path(path)) for path in source_before}
    report["source_bytes_unchanged"] = source_before == source_after
    report["all_expected"] = report["source_bytes_unchanged"] and all(
        row["matches_expected"] is not False for row in report["fixtures"])
    (output / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"{len(report['fixtures'])} fixtures; expected results matched: {report['all_expected']}; {output / 'results.json'}")
    return 0 if report["all_expected"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
