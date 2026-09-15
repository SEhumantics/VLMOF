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
ECORE_PRIMITIVE_URIS = {
    "boolean": "http://www.eclipse.org/emf/2002/Ecore#//EBoolean",
    "integer": "http://www.eclipse.org/emf/2002/Ecore#//EInt",
    "string": "http://www.eclipse.org/emf/2002/Ecore#//EString",
}


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


def native_identities(core, kind):
    """Return a bijection from Core IDs to native URIs, or retain every ambiguity."""
    values, problems, seen_uris = {}, [], {}
    for index, row in enumerate(core["provenance"]["identities"][kind]):
        if "id" not in row or "identity" not in row:
            problems.append({"kind": "malformed-provenance-row", "identity_kind": kind, "index": index})
            continue
        identifier, uri = row["id"], row["identity"]
        if identifier in values:
            problems.append({"kind": "duplicate-provenance-id", "identity_kind": kind, "id": identifier})
        if uri in seen_uris:
            problems.append({"kind": "duplicate-provenance-uri", "identity_kind": kind, "uri": uri})
        values[identifier], seen_uris[uri] = uri, identifier
    return values, problems


def normalized_value(value, object_ids, literal_ids):
    tag = value["tag"]
    if tag == "reference":
        return object_ids[value["object"]]
    if tag == "enumeration":
        return literal_ids[value["literal"]]
    return str(value["value"]).lower() if isinstance(value.get("value"), bool) else str(value["value"])


def check_identity_coverage(core, kind, identities, problems):
    """Require provenance IDs to cover the corresponding Core store exactly."""
    rows = core["snapshot"]["objects"] if kind == "objects" else core["schema"][kind]
    store_ids = [row["id"] for row in rows]
    if len(store_ids) != len(set(store_ids)):
        problems.append({"kind": "duplicate-core-store-id", "identity_kind": kind})
    if set(identities) != set(store_ids):
        problems.append({"kind": "provenance-store-coverage", "identity_kind": kind,
                         "provenance_ids": sorted(identities), "store_ids": sorted(set(store_ids))})


def loaded_identity_map(rows, uri_key, kind, problems, extra_key=None):
    values = {}
    for index, row in enumerate(rows):
        uri = row.get(uri_key)
        if not isinstance(uri, str) or not uri:
            problems.append({"kind": "malformed-loaded-identity", "identity_kind": kind, "index": index})
            continue
        if uri in values:
            problems.append({"kind": "duplicate-loaded-identity", "identity_kind": kind, "uri": uri})
        values[uri] = row.get(extra_key) if extra_key else row
    return values


def compare_loaded_to_core(emf_report, core):
    """Compare the actual loaded EObject feature lists with the bridge Core observation."""
    object_ids, problems = native_identities(core, "objects")
    class_ids, class_problems = native_identities(core, "classes")
    property_ids, property_problems = native_identities(core, "properties")
    enumeration_ids, enumeration_problems = native_identities(core, "enumerations")
    literal_ids, literal_problems = native_identities(core, "literals")
    problems.extend(class_problems)
    problems.extend(property_problems)
    problems.extend(enumeration_problems)
    problems.extend(literal_problems)
    for kind, identities in (("objects", object_ids), ("classes", class_ids),
                             ("properties", property_ids), ("enumerations", enumeration_ids),
                             ("literals", literal_ids)):
        check_identity_coverage(core, kind, identities, problems)
    declarations = emf_report.get("loaded_declarations", {})
    loaded_classes = loaded_identity_map(declarations.get("classes", []), "class_uri", "classes", problems)
    loaded_properties = loaded_identity_map(
        declarations.get("properties", []), "feature_uri", "properties", problems)
    loaded_enumerations = loaded_identity_map(
        declarations.get("enumerations", []), "enumeration_uri", "enumerations", problems)
    loaded_literals = loaded_identity_map(
        declarations.get("literals", []), "literal_uri", "literals", problems)
    for kind, loaded, identities in (("classes", loaded_classes, class_ids),
                                     ("properties", loaded_properties, property_ids),
                                     ("enumerations", loaded_enumerations, enumeration_ids),
                                     ("literals", loaded_literals, literal_ids)):
        if set(loaded) != set(identities.values()):
            problems.append({"kind": "loaded-provenance-coverage", "identity_kind": kind,
                             "loaded_uris": sorted(loaded),
                             "provenance_uris": sorted(set(identities.values()))})
    ordered = {row["id"]: row["multiplicity"]["ordered"] for row in core["schema"]["properties"]}
    declared_types = {row["id"]: row["type"]["tag"] for row in core["schema"]["properties"]}
    property_by_uri = {uri: identifier for identifier, uri in property_ids.items()}
    for row in core["schema"]["properties"]:
        native = loaded_properties.get(property_ids.get(row["id"]))
        if native is None:
            continue
        owner = row.get("owner", {})
        expected_owner = class_ids.get(owner.get("id")) if owner.get("tag") == "class" else None
        if native.get("owner_class_uri") != expected_owner:
            problems.append({"kind": "property-owner-mismatch", "property_id": row["id"],
                             "loaded_owner_uri": native.get("owner_class_uri"),
                             "core_owner_uri": expected_owner})
        if native.get("ordered") is not row["multiplicity"]["ordered"]:
            problems.append({"kind": "property-ordering-mismatch", "property_id": row["id"]})
        value_type = row.get("type", {})
        expected_type = (class_ids.get(value_type.get("id")) if value_type.get("tag") == "reference"
                         else enumeration_ids.get(value_type.get("id")) if value_type.get("tag") == "enumeration"
                         else ECORE_PRIMITIVE_URIS.get(value_type.get("tag")))
        if expected_type is not None and native.get("type_uri") != expected_type:
            problems.append({"kind": "property-type-mismatch", "property_id": row["id"],
                             "loaded_type_uri": native.get("type_uri"), "core_type_uri": expected_type})
    for row in core["schema"]["literals"]:
        native = loaded_literals.get(literal_ids.get(row["id"]))
        expected_enum = enumeration_ids.get(row["enumeration"])
        if native is not None and native.get("enumeration_uri") != expected_enum:
            problems.append({"kind": "literal-owner-mismatch", "literal_id": row["id"]})
    loaded_objects = loaded_identity_map(
        emf_report.get("loaded_objects", []), "object_uri", "objects", problems, "class_uri")
    core_objects = {}
    for index, row in enumerate(core["snapshot"]["objects"]):
        try:
            uri = object_ids[row["id"]]
            classifier = class_ids[row["classifier"]]
        except KeyError as error:
            problems.append({"kind": "unresolved-core-object-classifier", "index": index, "detail": str(error)})
            continue
        if uri in core_objects:
            problems.append({"kind": "duplicate-core-object-uri", "object_uri": uri, "index": index})
        core_objects[uri] = classifier
    object_mismatches = []
    for uri in sorted(set(loaded_objects) | set(core_objects)):
        if loaded_objects.get(uri) != core_objects.get(uri):
            object_mismatches.append({"object_uri": uri, "loaded_class_uri": loaded_objects.get(uri),
                                      "core_class_uri": core_objects.get(uri)})
    expected = {}
    for row in emf_report.get("loaded_observations", []):
        key = (row["object_uri"], row["feature_uri"])
        if key in expected:
            problems.append({"kind": "duplicate-loaded-observation-key", "object_uri": key[0], "feature_uri": key[1]})
        expected[key] = list(row["values"]) if row["is_set"] else []
    observed = {}
    for row in core["snapshot"]["observations"]:
        try:
            key = (object_ids[row["object"]], property_ids[row["property"]])
            for value in row["occurrences"]:
                if value.get("tag") != declared_types.get(row["property"]):
                    problems.append({"kind": "occurrence-tag-mismatch",
                                     "object_id": row["object"], "property_id": row["property"],
                                     "declared_tag": declared_types.get(row["property"]),
                                     "occurrence_tag": value.get("tag")})
                if value.get("tag") == "enumeration":
                    enum_uri = enumeration_ids[value["enumeration"]]
                    literal_uri = literal_ids[value["literal"]]
                    loaded_literal = loaded_literals.get(literal_uri)
                    if loaded_literal is None or loaded_literal.get("enumeration_uri") != enum_uri:
                        problems.append({"kind": "enumeration-literal-owner-mismatch",
                                         "literal_uri": literal_uri, "enumeration_uri": enum_uri})
            values = [normalized_value(value, object_ids, literal_ids) for value in row["occurrences"]]
        except KeyError as error:
            problems.append({"kind": "unresolved-core-identity", "detail": str(error)})
            continue
        if key in observed:
            problems.append({"kind": "duplicate-core-observation-key", "object_uri": key[0], "feature_uri": key[1]})
        observed[key] = values
    mismatches = []
    for key in sorted(set(expected) | set(observed)):
        left = expected[key] if key in expected else None
        right = observed[key] if key in observed else None
        property_id = property_by_uri.get(key[1])
        if property_id is not None and not ordered.get(property_id, True):
            if left is not None: left = sorted(left)
            if right is not None: right = sorted(right)
        if left != right:
            mismatches.append({"object_uri": key[0], "feature_uri": key[1],
                               "loaded_values": left, "core_values": right})
    return {"loaded_object_count": len(loaded_objects), "core_object_count": len(core_objects),
            "object_classifier_mismatches": object_mismatches,
            "loaded_observation_count": len(expected), "core_observation_count": len(observed),
            "lossless": not object_mismatches and not mismatches and not problems,
            "mismatches": mismatches, "problems": problems}


def eligible_for_timing(fixture, emf_status, vlmof_status, alignment):
    """Require an accepted, explicitly lossless positive condition before timing."""
    return bool(fixture.get("timing_eligible") and emf_status == "accepted" and
                vlmof_status == "accepted" and alignment and alignment.get("lossless") is True)


def valid_samples(samples, warmups, repetitions):
    if not isinstance(samples, list) or len(samples) != warmups + repetitions:
        return False
    return all(row.get("index") == index and row.get("warmup") is (index < warmups)
               and isinstance(row.get("nanoseconds"), int) and row["nanoseconds"] >= 0
               and row.get("accepted") is True for index, row in enumerate(samples))


def timing_complete(record, report, tool, warmups, repetitions):
    if record.get("exit") != 0 or not isinstance(report, dict):
        return False
    if tool == "emf":
        return (report.get("timing_boundary") == "preloaded-schema-and-instance-validation"
                and report.get("all_timed_results_accepted") is True
                and valid_samples(report.get("samples"), warmups, repetitions))
    return (valid_samples(report.get("schema"), warmups, repetitions)
            and valid_samples(report.get("schemaAndSnapshot"), warmups, repetitions))


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
    parser.add_argument("--timing-order", choices=("emf-first", "vlmof-first"), default="emf-first",
                        help="Counterbalance the two independent timing processes.")
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

        alignment = None
        core = output / "normalized" / f"{fixture_row['id']}.e1.json"
        source_args = ["import", *[(manifest_path.parent / path).resolve() for path in fixture["ecore"]], "--",
                       *[(manifest_path.parent / path).resolve() for path in fixture["xmi"]]]
        normalization_record, normalization_stdout = command(
            f"{fixture_row['id']}-normalize", bridge_command(INTERCHANGE, source_args), output)
        normalization_json = json_output(normalization_record, normalization_stdout)
        if normalization_json is not None:
            core.write_text(json.dumps(normalization_json, indent=2) + "\n", encoding="utf-8")
            alignment = compare_loaded_to_core(emf_report or {}, normalization_json)
            normalization_status = "accepted" if alignment["lossless"] else "normalization-loss"
            fixture_row["phases"]["normalization"] = {"status": normalization_status, "record": normalization_record,
                                                        "core": str(core.relative_to(output)), "sha256": digest(core),
                                                        "loaded_to_core": alignment}
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
            fixture_row["matches_expected"] = bool(alignment and alignment["lossless"]) and all(observed.get(key) == value for key, value in expected.items())
        if args.measure and eligible_for_timing(
                fixture, emf_status, fixture_row["phases"]["vlmof_validation"]["status"], alignment):
            actions = {
                "emf": (f"{fixture_row['id']}-emf-warm",
                    bridge_command(HARNESS, ["warm-validate", manifest_path, args.warmups, args.repetitions])),
                "lean": (f"{fixture_row['id']}-lean-warm",
                    [str(ROOT / ".lake" / "build" / "bin" / "validationBench"), str(core), str(args.warmups), str(args.repetitions)])}
            order = ("emf", "lean") if args.timing_order == "emf-first" else ("lean", "emf")
            timing_results = {}
            for tool in order:
                name, invocation = actions[tool]
                timing_results[tool] = command(name, invocation, output)
            emf_timing, emf_timing_stdout = timing_results["emf"]
            lean_timing, lean_timing_stdout = timing_results["lean"]
            emf_timing_report = json_output(emf_timing, emf_timing_stdout)
            lean_timing_report = json_output(lean_timing, lean_timing_stdout)
            emf_complete = timing_complete(emf_timing, emf_timing_report, "emf", args.warmups, args.repetitions)
            lean_complete = timing_complete(lean_timing, lean_timing_report, "lean", args.warmups, args.repetitions)
            fixture_row["timing"] = {"emf": {"record": emf_timing, "report": emf_timing_report,
                                                "complete": emf_complete},
                                      "lean": {"record": lean_timing, "report": lean_timing_report,
                                                 "complete": lean_complete},
                                      "complete": emf_complete and lean_complete,
                                      "execution_order": list(order)}
        report["fixtures"].append(fixture_row)

    source_after = {path: digest(Path(path)) for path in source_before}
    report["source_bytes_unchanged"] = source_before == source_after
    report["all_requested_timings_complete"] = (not args.measure) or all(
        row.get("timing", {}).get("complete") is True
        for row in report["fixtures"] if json.loads(Path(row["manifest"]).read_text()).get("timing_eligible"))
    report["all_expected"] = report["source_bytes_unchanged"] and report["all_requested_timings_complete"] and all(
        row["matches_expected"] is not False for row in report["fixtures"])
    (output / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"{len(report['fixtures'])} fixtures; expected results matched: {report['all_expected']}; {output / 'results.json'}")
    return 0 if report["all_expected"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
