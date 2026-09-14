#!/usr/bin/env python3
"""Run the pinned public EMF evaluation and retain reproducible evidence.

The Train and EMF Compare arguments must be clean Git checkouts at the revisions
named below.  OUTPUT must not exist.  Raw public files are read and hashed but
never modified; every adaptation and generated resource is written under OUTPUT.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "bridge"
TRAIN_REVISION = "6490047d7449f9a4b66cec032b9377bfc06a54d2"
EMF_COMPARE_REVISION = "9f25a964c1be423373587d8063a5b132714ebeae"
TRAIN_STEMS = (
    "railway-batch-1",
    "railway-batch-2",
    "railway-inject-1",
    "railway-inject-2",
    "railway-repair-1",
    "railway-repair-2",
)
STATUS_VALUES = ("accepted", "rejected", "unsupported", "not-run", "execution-failure")


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def probe(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=30)


def validate_checkout(path: Path, expected: str, label: str, relevant_paths: list[str]) -> None:
    if not path.is_dir():
        raise ValueError(f"{label} checkout is not a directory: {path}")
    revision = probe(["git", "rev-parse", "HEAD"], path)
    if revision.returncode != 0:
        raise ValueError(f"cannot read {label} revision: {revision.stderr.strip()}")
    observed = revision.stdout.strip()
    if observed != expected:
        raise ValueError(f"unexpected {label} revision: expected {expected}, observed {observed}")
    tracked = probe(["git", "ls-files", "--error-unmatch", "--", *relevant_paths], path)
    if tracked.returncode != 0:
        raise ValueError(f"{label} evaluated sources are not tracked at the pin")
    changed = probe(["git", "diff", "--quiet", "HEAD", "--", *relevant_paths], path)
    if changed.returncode != 0:
        if changed.returncode == 1:
            raise ValueError(f"{label} evaluated sources differ from the pinned commit")
        raise ValueError(f"cannot compare {label} evaluated sources with the pin")


def required_file(path: Path, label: str) -> Path:
    if not path.is_file():
        raise ValueError(f"missing {label}: {path}")
    return path


def file_record(path: Path, relative_to: Path | None = None) -> dict[str, Any]:
    display = path
    if relative_to is not None:
        try:
            display = path.relative_to(relative_to)
        except ValueError:
            pass
    return {"path": str(display), "bytes": path.stat().st_size, "sha256": digest(path)}


class Recorder:
    def __init__(self, output: Path, report: dict[str, Any]):
        self.output = output
        self.commands = output / "commands"
        self.commands.mkdir()
        self.report = report
        self.sequence = 0

    def save(self) -> None:
        temporary = self.output / "results.json.tmp"
        temporary.write_text(json.dumps(self.report, indent=2) + "\n", encoding="utf-8")
        temporary.replace(self.output / "results.json")

    def run(
        self,
        label: str,
        args: Iterable[object],
        *,
        cwd: Path = ROOT,
        timeout: int = 600,
        stdout_path: Path | None = None,
    ) -> dict[str, Any]:
        command = [str(item) for item in args]
        self.sequence += 1
        prefix = f"{self.sequence:03d}-{label}"
        stdout_file = stdout_path or self.commands / f"{prefix}.stdout"
        stderr_file = self.commands / f"{prefix}.stderr"
        stdout_file.parent.mkdir(parents=True, exist_ok=True)
        started = utc_now()
        begin = time.perf_counter()
        error = None
        timed_out = False
        exit_code = None
        out = b""
        err = b""
        try:
            result = subprocess.run(command, cwd=cwd, capture_output=True, timeout=timeout)
            exit_code, out, err = result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired as failure:
            timed_out = True
            error = str(failure)
            out = failure.stdout or b""
            err = failure.stderr or b""
        except OSError as failure:
            error = f"{type(failure).__name__}: {failure}"
        elapsed = time.perf_counter() - begin
        stdout_file.write_bytes(out)
        stderr_file.write_bytes(err)
        record = {
            "id": self.sequence,
            "label": label,
            "command": command,
            "cwd": str(cwd),
            "started_utc": started,
            "duration_seconds": elapsed,
            "exit": exit_code,
            "timed_out": timed_out,
            "stdout": file_record(stdout_file, self.output),
            "stderr": file_record(stderr_file, self.output),
        }
        if error is not None:
            record["error"] = error
        self.report["commands"].append(record)
        self.save()
        return record


def output_bytes(record: dict[str, Any], output: Path, stream: str = "stdout") -> bytes:
    return (output / record[stream]["path"]).read_bytes()


def output_text(record: dict[str, Any], output: Path, stream: str = "stdout") -> str:
    return output_bytes(record, output, stream).decode("utf-8", errors="replace")


def accepted_process(record: dict[str, Any]) -> str:
    return "accepted" if record["exit"] == 0 else "execution-failure"


def classify_bridge(record: dict[str, Any], output: Path) -> str:
    if record["exit"] is None:
        return "execution-failure"
    if record["exit"] == 0:
        return "accepted"
    diagnostics = output_text(record, output) + output_text(record, output, "stderr")
    if "REJECT" in diagnostics:
        return "rejected"
    return "execution-failure"


def classify_checker(record: dict[str, Any], output: Path) -> tuple[str, dict[str, Any] | None]:
    if record["exit"] is None:
        return "execution-failure", None
    try:
        document = json.loads(output_text(record, output))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return "execution-failure", None
    status = document.get("status") if isinstance(document, dict) else None
    classes = {
        "accepted": "accepted",
        "invalid": "rejected",
        "malformed": "rejected",
        "parse-malformed": "rejected",
        "binding-failure": "rejected",
        "unsupported": "unsupported",
    }
    exits = {
        "accepted": 0,
        "invalid": 1,
        "malformed": 2,
        "parse-malformed": 2,
        "binding-failure": 2,
        "unsupported": 3,
    }
    if status not in classes or record["exit"] != exits[status]:
        return "execution-failure", document if isinstance(document, dict) else None
    return classes[status], document


def step(label: str, status: str, execution: dict[str, Any] | None = None, **extra: Any) -> dict[str, Any]:
    if status not in STATUS_VALUES:
        raise ValueError(f"unknown result classification: {status}")
    result: dict[str, Any] = {"step": label, "status": status}
    if execution is not None:
        result["command_id"] = execution["id"]
    result.update(extra)
    return result


def verify_generated(paths: Iterable[Path]) -> bool:
    return all(path.is_file() for path in paths)


def artifact_records(paths: Iterable[Path], output: Path) -> list[dict[str, Any]]:
    return [file_record(path, output) for path in paths if path.is_file()]


def train_default_summary(document: dict[str, Any]) -> dict[str, Any]:
    properties = {
        row.get("name"): row
        for row in document.get("schema", {}).get("properties", [])
        if row.get("name") in {"position", "currentPosition"}
    }
    observations = document.get("snapshot", {}).get("observations", [])
    summary: dict[str, Any] = {}
    for name in ("position", "currentPosition"):
        row = properties.get(name)
        if row is None:
            continue
        selected = [item for item in observations if item.get("property") == row.get("id")]
        summary[name] = {
            "property_id": row.get("id"),
            "lower": row.get("multiplicity", {}).get("lower"),
            "observation_count": len(selected),
            "empty_observation_count": sum(not item.get("occurrences") for item in selected),
        }
    return summary


def not_run_steps(names: Iterable[str], reason: str) -> list[dict[str, Any]]:
    return [step(name, "not-run", reason=reason) for name in names]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train", required=True, type=Path, help="pinned Train benchmark checkout")
    parser.add_argument("--emf-compare", required=True, type=Path, help="pinned EMF Compare checkout")
    parser.add_argument("--output", required=True, type=Path, help="new evidence directory")
    args = parser.parse_args()

    train = args.train.resolve(strict=True)
    emf_compare = args.emf_compare.resolve(strict=True)
    output = args.output.resolve()
    try:
        train_relevant = [
            "trainbenchmark-format-emf-model/src/railway.xcore",
            *(f"models/{stem}.xmi" for stem in TRAIN_STEMS),
        ]
        compare_relevant = ["plugins/org.eclipse.emf.compare/model/compare.ecore"]
        validate_checkout(train, TRAIN_REVISION, "Train", train_relevant)
        validate_checkout(emf_compare, EMF_COMPARE_REVISION, "EMF Compare", compare_relevant)
        xcore = required_file(
            train / "trainbenchmark-format-emf-model/src/railway.xcore", "Train Xcore metamodel"
        )
        train_inputs = {
            stem: required_file(train / "models" / f"{stem}.xmi", f"Train snapshot {stem}")
            for stem in TRAIN_STEMS
        }
        compare_ecore = required_file(
            emf_compare / "plugins/org.eclipse.emf.compare/model/compare.ecore",
            "EMF Compare metamodel",
        )
        tiny_xmi = required_file(BRIDGE / "src/main/resources/samples/tiny.xmi", "bridge probe XMI")
        checker = Path(os.environ.get("CHECKER", ROOT / ".lake/build/bin/vlmof")).resolve(strict=True)
        if not os.access(checker, os.X_OK):
            raise ValueError(f"checker is not executable: {checker}")
        output.mkdir(parents=True, exist_ok=False)
    except (FileExistsError, FileNotFoundError, ValueError) as failure:
        print(f"public evaluation setup failed: {failure}", file=sys.stderr)
        return 2

    started = time.perf_counter()
    report: dict[str, Any] = {
        "schema": "vlmof-public-evaluation-1",
        "scope": (
            "Pinned Train Xcore and six explicitly adapted XMI snapshots through EMF import, "
            "Lean Core checking, fresh EMF export, reimport, native-identity-map comparison, and "
            "a second Core check; negative controls for the unadapted Train metamodel and one "
            "unadapted Train snapshot; pinned EMF Compare rejection at the declared E1 profile boundary."
        ),
        "started_utc": utc_now(),
        "classifications": {
            "accepted": "the requested stage completed and its structured success result was validated",
            "rejected": "the input was processed and rejected inside the declared mapping or Core domain",
            "unsupported": "a pinned public construct is outside the declared E1 mapping profile",
            "not-run": "a prerequisite failed, so the dependent stage was not invoked",
            "execution-failure": "the tool failed to execute or returned an inconsistent/unparseable result",
        },
        "timing_policy": (
            "Durations are single-run operational wall-clock records. They are not statistical "
            "benchmarks and support no performance-superiority claim."
        ),
        "paths": {
            "repository": str(ROOT),
            "train_checkout": str(train),
            "emf_compare_checkout": str(emf_compare),
            "checker": str(checker),
            "output": str(output),
        },
        "commands": [],
        "setup": [],
        "cases": [],
        "all_expected": False,
    }
    recorder = Recorder(output, report)

    own_revision = recorder.run("repository-revision", ["git", "rev-parse", "HEAD"])
    own_dirty = recorder.run(
        "repository-status", ["git", "status", "--porcelain", "--untracked-files=all"]
    )
    train_revision = recorder.run("train-revision", ["git", "rev-parse", "HEAD"], cwd=train)
    train_dirty = recorder.run(
        "train-status", ["git", "status", "--porcelain", "--untracked-files=all"], cwd=train
    )
    compare_revision = recorder.run("emf-compare-revision", ["git", "rev-parse", "HEAD"], cwd=emf_compare)
    compare_dirty = recorder.run(
        "emf-compare-status",
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=emf_compare,
    )
    train_sources = recorder.run(
        "train-evaluated-sources-diff",
        ["git", "diff", "--quiet", "HEAD", "--", *train_relevant],
        cwd=train,
    )
    compare_sources = recorder.run(
        "emf-compare-evaluated-sources-diff",
        ["git", "diff", "--quiet", "HEAD", "--", *compare_relevant],
        cwd=emf_compare,
    )
    checker_root_record = recorder.run(
        "checker-repository-root", ["git", "rev-parse", "--show-toplevel"], cwd=checker.parent
    )
    checker_root_text = output_text(checker_root_record, output).strip()
    checker_root = Path(checker_root_text) if checker_root_record["exit"] == 0 else None
    checker_revision = (
        recorder.run("checker-repository-revision", ["git", "rev-parse", "HEAD"], cwd=checker_root)
        if checker_root is not None
        else None
    )
    checker_dirty = (
        recorder.run(
            "checker-repository-status",
            ["git", "status", "--porcelain", "--untracked-files=all"],
            cwd=checker_root,
        )
        if checker_root is not None
        else None
    )
    report["repository"] = {
        "commit": output_text(own_revision, output).strip(),
        "dirty": bool(output_text(own_dirty, output).strip()),
    }
    report["public_checkouts"] = {
        "train": {
            "expected_commit": TRAIN_REVISION,
            "observed_commit": output_text(train_revision, output).strip(),
            "dirty": bool(output_text(train_dirty, output).strip()),
            "evaluated_sources": train_relevant,
            "evaluated_sources_match_commit": train_sources["exit"] == 0,
            "source_diff_command_id": train_sources["id"],
        },
        "emf_compare": {
            "expected_commit": EMF_COMPARE_REVISION,
            "observed_commit": output_text(compare_revision, output).strip(),
            "dirty": bool(output_text(compare_dirty, output).strip()),
            "evaluated_sources": compare_relevant,
            "evaluated_sources_match_commit": compare_sources["exit"] == 0,
            "source_diff_command_id": compare_sources["id"],
        },
    }
    report["checker"] = {
        **file_record(checker),
        "repository_root": checker_root_text or None,
        "repository_commit": output_text(checker_revision, output).strip() if checker_revision else None,
        "repository_dirty": bool(output_text(checker_dirty, output).strip()) if checker_dirty else None,
    }

    environment_commands = {
        "python": recorder.run("python-version", [sys.executable, "--version"]),
        "java": recorder.run("java-version", ["java", "-version"]),
        "maven": recorder.run("maven-version", ["mvn", "-version"]),
        "lean": recorder.run("lean-version", ["lake", "env", "lean", "--version"]),
        "kernel": recorder.run("kernel-version", ["uname", "-a"]),
        "cpu": recorder.run("cpu-information", ["lscpu"]),
    }
    report["environment"] = {
        "platform": platform.platform(),
        "machine": platform.machine(),
        "processor": platform.processor(),
        "logical_cpu_count": os.cpu_count(),
        "python_runtime": sys.version,
        "command_ids": {name: record["id"] for name, record in environment_commands.items()},
    }

    source_files = [xcore, *train_inputs.values(), compare_ecore, tiny_xmi]
    implementation_files = [
        Path(__file__).resolve(),
        BRIDGE / "pom.xml",
        BRIDGE / "scripts/adapt_train_defaults.py",
        BRIDGE / "scripts/run_train_e1.sh",
        BRIDGE / "scripts/run_train_roundtrip_review.sh",
        BRIDGE / "src/main/java/org/vlmof/bridge/XcoreToEcore.java",
        BRIDGE / "src/main/java/org/vlmof/bridge/StripEcoreAnnotations.java",
        BRIDGE / "src/main/java/org/vlmof/bridge/EmfInterchange.java",
        BRIDGE / "src/main/java/org/vlmof/bridge/IdentityCorrespondence.java",
    ]
    report["input_manifest_before"] = [file_record(path) for path in source_files]
    report["implementation_manifest"] = [file_record(path, ROOT) for path in implementation_files]
    recorder.save()

    compile_record = recorder.run(
        "bridge-test-compile", ["mvn", "-q", "-f", BRIDGE / "pom.xml", "test-compile"], timeout=900
    )
    compile_status = accepted_process(compile_record)
    report["setup"].append(step("compile-bridge", compile_status, compile_record))

    artifacts = output / "artifacts"
    artifacts.mkdir()
    generated_ecore = artifacts / "railway.generated.ecore"
    profile_ecore = artifacts / "railway.profile.ecore"
    profile_manifest = artifacts / "railway.profile.manifest.json"
    if compile_status == "accepted":
        xcore_record = recorder.run(
            "compile-train-xcore",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.XcoreToEcore",
                f"-Dexec.args={xcore} {generated_ecore}",
            ],
            timeout=900,
        )
        xcore_status = accepted_process(xcore_record)
        if xcore_status == "accepted" and not verify_generated([generated_ecore]):
            xcore_status = "execution-failure"
        report["setup"].append(
            step(
                "compile-xcore", xcore_status, xcore_record,
                artifacts=artifact_records([generated_ecore], output),
            )
        )
    else:
        xcore_status = "not-run"
        report["setup"].append(step("compile-xcore", xcore_status, reason="bridge compilation failed"))

    if xcore_status == "accepted":
        profile_record = recorder.run(
            "adapt-train-metamodel",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.StripEcoreAnnotations",
                f"-Dexec.args={generated_ecore} {profile_ecore} {xcore} {profile_manifest}",
            ],
            timeout=900,
        )
        profile_status = accepted_process(profile_record)
        if profile_status == "accepted" and not verify_generated([profile_ecore, profile_manifest]):
            profile_status = "execution-failure"
        report["setup"].append(
            step(
                "adapt-metamodel", profile_status, profile_record,
                artifacts=artifact_records([profile_ecore, profile_manifest], output),
            )
        )
    else:
        profile_status = "not-run"
        report["setup"].append(step("adapt-metamodel", profile_status, reason="Xcore compilation failed"))
    recorder.save()

    controls = output / "controls"
    controls.mkdir()
    raw_metamodel_case: dict[str, Any] = {
        "id": "train-unadapted-generated-metamodel",
        "origin": "Xcore compiler output before the explicit profile adaptation",
        "expected_status": "unsupported",
        "expectation": "Generator annotations are outside the declared E1 mapping profile.",
        "steps": [],
    }
    if xcore_status == "accepted":
        raw_metamodel_record = recorder.run(
            "train-unadapted-metamodel-import",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.EmfInterchange",
                f"-Dexec.args=import {generated_ecore} -- {train_inputs[TRAIN_STEMS[0]]}",
            ],
            timeout=900,
        )
        raw_metamodel_diagnostics = (
            output_text(raw_metamodel_record, output)
            + output_text(raw_metamodel_record, output, "stderr")
        )
        if raw_metamodel_record["exit"] != 0 and "REJECT annotation" in raw_metamodel_diagnostics:
            raw_metamodel_status = "unsupported"
        else:
            observed = classify_bridge(raw_metamodel_record, output)
            raw_metamodel_status = "execution-failure" if observed == "accepted" else observed
        raw_metamodel_case["steps"].append(
            step("profile-import", raw_metamodel_status, raw_metamodel_record)
        )
    else:
        raw_metamodel_status = "not-run"
        raw_metamodel_case["steps"].append(
            step("profile-import", raw_metamodel_status, reason="Xcore compilation failed")
        )
    raw_metamodel_case["status"] = raw_metamodel_status
    raw_metamodel_case["matches_expectation"] = raw_metamodel_status == "unsupported"
    report["cases"].append(raw_metamodel_case)

    raw_snapshot_case: dict[str, Any] = {
        "id": "train-batch-1-unadapted-snapshot",
        "origin": "Train benchmark public snapshot before default materialization",
        "expected_status": "accepted",
        "expectation": (
            "Core accepts the optional empty observations; six absent values for each enum "
            "show why explicit default materialization is needed to preserve runtime-default meaning."
        ),
        "input": file_record(train_inputs[TRAIN_STEMS[0]]),
        "steps": [],
    }
    if profile_status == "accepted":
        raw_imported = controls / "railway-batch-1.raw.e1.json"
        raw_import_record = recorder.run(
            "train-batch-1-raw-import",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.EmfInterchange",
                f"-Dexec.args=import {profile_ecore} -- {train_inputs[TRAIN_STEMS[0]]}",
            ],
            timeout=900,
            stdout_path=raw_imported,
        )
        raw_import_status = classify_bridge(raw_import_record, output)
        if raw_import_status == "accepted":
            try:
                raw_document = json.loads(raw_imported.read_text(encoding="utf-8"))
                if raw_document.get("version") != "vlmof-e1-1":
                    raw_import_status = "execution-failure"
            except (OSError, json.JSONDecodeError, AttributeError):
                raw_import_status = "execution-failure"
        raw_snapshot_case["steps"].append(
            step(
                "import", raw_import_status, raw_import_record,
                artifacts=artifact_records([raw_imported], output),
            )
        )
        if raw_import_status == "accepted":
            raw_check_path = controls / "railway-batch-1.raw.check.json"
            raw_check_record = recorder.run(
                "train-batch-1-raw-core-check",
                [checker, "check-json", raw_imported],
                stdout_path=raw_check_path,
                timeout=900,
            )
            raw_check_status, raw_check_document = classify_checker(raw_check_record, output)
            raw_snapshot_case["steps"].append(
                step(
                    "core-check", raw_check_status, raw_check_record,
                    observed=raw_check_document,
                    artifacts=artifact_records([raw_check_path], output),
                )
            )
            raw_snapshot_status = raw_check_status
            summary = train_default_summary(raw_document)
            raw_snapshot_case["default_observation_summary"] = summary
            raw_snapshot_matches = (
                raw_check_status == "accepted"
                and set(summary) == {"position", "currentPosition"}
                and all(
                    item["lower"] == 0 and item["empty_observation_count"] == 6
                    for item in summary.values()
                )
            )
        else:
            raw_snapshot_case["steps"].append(
                step("core-check", "not-run", reason="raw snapshot import was not accepted")
            )
            raw_snapshot_status = raw_import_status
            raw_snapshot_matches = False
    else:
        raw_snapshot_case["steps"].extend(
            not_run_steps(("import", "core-check"), "profile metamodel preparation failed")
        )
        raw_snapshot_status = "not-run"
        raw_snapshot_matches = False
    raw_snapshot_case["status"] = raw_snapshot_status
    raw_snapshot_case["matches_expectation"] = raw_snapshot_matches
    report["cases"].append(raw_snapshot_case)
    recorder.save()

    remaining_names = ("import", "core-check", "fresh-export", "reimport", "identity-map-compare", "core-recheck")
    for stem, original in train_inputs.items():
        case_dir = output / "cases" / stem
        case_dir.mkdir(parents=True)
        adapted = case_dir / "adapted.xmi"
        adaptation_manifest = case_dir / "adaptation.manifest.json"
        case: dict[str, Any] = {
            "id": stem,
            "origin": "Train benchmark public snapshot",
            "expected_status": "accepted",
            "original": file_record(original),
            "steps": [],
        }
        if profile_status != "accepted":
            case["steps"] = not_run_steps(
                ("adapt-instance", *remaining_names), "metamodel preparation did not complete"
            )
            case["status"] = "not-run"
            case["matches_expectation"] = False
            report["cases"].append(case)
            recorder.save()
            continue

        adapt_record = recorder.run(
            f"{stem}-adapt-instance",
            [sys.executable, BRIDGE / "scripts/adapt_train_defaults.py", original, adapted, adaptation_manifest],
        )
        adapt_status = accepted_process(adapt_record)
        if adapt_status == "accepted" and not verify_generated([adapted, adaptation_manifest]):
            adapt_status = "execution-failure"
        case["steps"].append(
            step(
                "adapt-instance", adapt_status, adapt_record,
                artifacts=artifact_records([adapted, adaptation_manifest], output),
            )
        )
        if adapt_status == "accepted":
            try:
                case["adaptation_manifest"] = json.loads(adaptation_manifest.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                adapt_status = "execution-failure"
                case["steps"][-1]["status"] = adapt_status
                case["steps"][-1]["reason"] = "adaptation manifest is not valid JSON"
        if adapt_status != "accepted":
            case["steps"].extend(not_run_steps(remaining_names, "instance adaptation failed"))
            case["status"] = adapt_status
            case["matches_expectation"] = False
            report["cases"].append(case)
            recorder.save()
            continue

        imported = case_dir / "imported.e1.json"
        import_record = recorder.run(
            f"{stem}-import",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.EmfInterchange",
                f"-Dexec.args=import {profile_ecore} -- {adapted}",
            ],
            timeout=900,
            stdout_path=imported,
        )
        import_status = classify_bridge(import_record, output)
        if import_status == "accepted":
            try:
                imported_document = json.loads(imported.read_text(encoding="utf-8"))
                if imported_document.get("version") != "vlmof-e1-1":
                    import_status = "execution-failure"
            except (OSError, json.JSONDecodeError, AttributeError):
                import_status = "execution-failure"
        case["steps"].append(
            step("import", import_status, import_record, artifacts=artifact_records([imported], output))
        )
        if import_status != "accepted":
            case["steps"].extend(not_run_steps(remaining_names[1:], "EMF import was not accepted"))
            case["status"] = import_status
            case["matches_expectation"] = False
            report["cases"].append(case)
            recorder.save()
            continue

        check_path = case_dir / "check.json"
        check_record = recorder.run(
            f"{stem}-core-check", [checker, "check-json", imported], stdout_path=check_path, timeout=900
        )
        check_status, check_document = classify_checker(check_record, output)
        case["steps"].append(
            step(
                "core-check", check_status, check_record,
                observed=check_document,
                artifacts=artifact_records([check_path], output),
            )
        )
        if check_status != "accepted":
            case["steps"].extend(not_run_steps(remaining_names[2:], "initial Core check was not accepted"))
            case["status"] = check_status
            case["matches_expectation"] = False
            report["cases"].append(case)
            recorder.save()
            continue

        exported_ecore = case_dir / "exported.ecore"
        exported_xmi = case_dir / "exported.xmi"
        identity_map = case_dir / "exported.xmi.ids.json"
        export_record = recorder.run(
            f"{stem}-fresh-export",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.EmfInterchange",
                f"-Dexec.args=export {imported} {exported_ecore} {exported_xmi}",
            ],
            timeout=900,
        )
        export_status = accepted_process(export_record)
        if export_status == "accepted" and not verify_generated([exported_ecore, exported_xmi, identity_map]):
            export_status = "execution-failure"
        case["steps"].append(
            step(
                "fresh-export", export_status, export_record,
                artifacts=artifact_records([exported_ecore, exported_xmi, identity_map], output),
            )
        )
        if export_status != "accepted":
            case["steps"].extend(not_run_steps(remaining_names[3:], "fresh EMF export failed"))
            case["status"] = export_status
            case["matches_expectation"] = False
            report["cases"].append(case)
            recorder.save()
            continue

        reimported = case_dir / "reimported.e1.json"
        reimport_record = recorder.run(
            f"{stem}-reimport",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.EmfInterchange",
                f"-Dexec.args=import {exported_ecore} -- {exported_xmi}",
            ],
            timeout=900,
            stdout_path=reimported,
        )
        reimport_status = classify_bridge(reimport_record, output)
        if reimport_status == "accepted":
            try:
                reimported_document = json.loads(reimported.read_text(encoding="utf-8"))
                if reimported_document.get("version") != "vlmof-e1-1":
                    reimport_status = "execution-failure"
            except (OSError, json.JSONDecodeError, AttributeError):
                reimport_status = "execution-failure"
        case["steps"].append(
            step("reimport", reimport_status, reimport_record, artifacts=artifact_records([reimported], output))
        )
        if reimport_status != "accepted":
            case["steps"].extend(not_run_steps(remaining_names[4:], "fresh EMF resource reimport failed"))
            case["status"] = reimport_status
            case["matches_expectation"] = False
            report["cases"].append(case)
            recorder.save()
            continue

        compare_path = case_dir / "compare.txt"
        compare_record = recorder.run(
            f"{stem}-identity-map-compare",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.EmfInterchange",
                f"-Dexec.args=compare {imported} {reimported} {identity_map}",
            ],
            timeout=900,
            stdout_path=compare_path,
        )
        compare_status = classify_bridge(compare_record, output)
        if compare_status == "accepted" and "ROUNDTRIP OK" not in output_text(compare_record, output):
            compare_status = "execution-failure"
        case["steps"].append(
            step(
                "identity-map-compare", compare_status, compare_record,
                identity_map=file_record(identity_map, output),
                artifacts=artifact_records([compare_path], output),
            )
        )
        if compare_status != "accepted":
            case["steps"].extend(not_run_steps(("core-recheck",), "identity-map comparison failed"))
            case["status"] = compare_status
            case["matches_expectation"] = False
            report["cases"].append(case)
            recorder.save()
            continue

        recheck_path = case_dir / "recheck.json"
        recheck_record = recorder.run(
            f"{stem}-core-recheck", [checker, "check-json", reimported],
            stdout_path=recheck_path,
            timeout=900,
        )
        recheck_status, recheck_document = classify_checker(recheck_record, output)
        case["steps"].append(
            step(
                "core-recheck", recheck_status, recheck_record,
                observed=recheck_document,
                artifacts=artifact_records([recheck_path], output),
            )
        )
        case["status"] = recheck_status
        case["matches_expectation"] = recheck_status == "accepted"
        report["cases"].append(case)
        recorder.save()

    emf_case: dict[str, Any] = {
        "id": "emf-compare-operations",
        "origin": "EMF Compare public compare.ecore",
        "expected_status": "unsupported",
        "expectation": "EOperations are outside the declared E1 mapping profile.",
        "input": file_record(compare_ecore),
        "steps": [],
    }
    if compile_status == "accepted":
        emf_record = recorder.run(
            "emf-compare-import",
            [
                "mvn", "-q", "-f", BRIDGE / "pom.xml", "exec:java",
                "-Dexec.mainClass=org.vlmof.bridge.EmfInterchange",
                f"-Dexec.args=import {compare_ecore} -- {tiny_xmi}",
            ],
            timeout=900,
        )
        emf_diagnostics = output_text(emf_record, output) + output_text(emf_record, output, "stderr")
        if emf_record["exit"] != 0 and "REJECT operation" in emf_diagnostics:
            emf_status = "unsupported"
        else:
            observed = classify_bridge(emf_record, output)
            emf_status = "execution-failure" if observed == "accepted" else observed
        emf_case["steps"].append(step("profile-import", emf_status, emf_record))
    else:
        emf_status = "not-run"
        emf_case["steps"].append(step("profile-import", emf_status, reason="bridge compilation failed"))
    emf_case["status"] = emf_status
    emf_case["matches_expectation"] = emf_status == "unsupported"
    report["cases"].append(emf_case)

    report["input_manifest_after"] = [file_record(path) for path in source_files]
    report["raw_inputs_unchanged"] = report["input_manifest_before"] == report["input_manifest_after"]
    report["finished_utc"] = utc_now()
    report["evaluation_wall_seconds"] = time.perf_counter() - started
    report["status_counts"] = {
        status: sum(case.get("status") == status for case in report["cases"])
        for status in STATUS_VALUES
    }
    report["all_expected"] = (
        all(item["status"] == "accepted" for item in report["setup"])
        and all(case["matches_expectation"] for case in report["cases"])
        and report["raw_inputs_unchanged"]
        and report["public_checkouts"]["train"]["observed_commit"] == TRAIN_REVISION
        and report["public_checkouts"]["emf_compare"]["observed_commit"] == EMF_COMPARE_REVISION
        and report["public_checkouts"]["train"]["evaluated_sources_match_commit"]
        and report["public_checkouts"]["emf_compare"]["evaluated_sources_match_commit"]
    )
    recorder.save()
    print(
        f"{len(TRAIN_STEMS)} adapted Train cases and 3 boundary/control cases; "
        f"expectations matched: {report['all_expected']}; {output / 'results.json'}"
    )
    return 0 if report["all_expected"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
