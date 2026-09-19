#!/usr/bin/env python3
"""Trace evaluation evidence to the paper's Tables 1 and 2, and check companion evidence.

  table1 RESULTS.json [...]  Table 1 rows from run_emf_validation.py reports
  table2 RUN_DIR             Table 2 from a run_fifth_evaluation.py directory
  companion ROOT             verify retained evidence against companion-evidence.json
  manifest WORKSPACE OUT     regenerate that manifest from the author workspace

The printed paper values are parsed from paper/sections/*.tex. Validation decisions
and object/row counts of a fresh run are expected to equal them; measured times are
new observations and are shown beside the historical values, never substituted.
Nothing here modifies evidence.
"""

import argparse
import hashlib
import json
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
from run_emf_validation import valid_samples  # noqa: E402

EVALUATION_TEX = ROOT / "paper" / "sections" / "evaluation.tex"
TIMES_TEX = ROOT / "paper" / "sections" / "validation-times.tex"
COMPANION = ROOT / "experiments" / "companion-evidence.json"

SCALING = ([f"containment-inheritance-{n}" for n in (11, 101, 501)]
           + [f"train-projection-{n}" for n in (10, 100, 500)]
           + [f"recursive-containment-{n}" for n in (11, 101, 501)])
# Table 1(a) row label -> fixture ids (experiments/cases/emf-validation, or the two
# Train manifests written by the public phase / retained in companion evidence).
TABLE1_FIXTURES = {
    "Aligned positives (11)": ["tiny-valid", "train-route-switch", *SCALING],
    "Missing required String": ["tiny-missing-required"],
    "Repeated unique String": ["unique-duplicate-source"],
    "Train with explicit defaults": ["train-batch-1-profile"],
    "Train with original omissions": ["public-train-raw-batch-1-profile"],
    "Lower 1 / upper 0": ["invalid-bounds"],
    "Empty 0..0": ["zero-upper"],
    "Repeated containment": ["unpaired-repeated-containment"],
    "Two unpaired features": ["unpaired-two-feature-containment"],
}
# Table 1(b): state comparison after loading; every other fixture is "match".
TABLE1_STATE = {
    "train-batch-1-profile": "12 scalar-presence differences",
    "unpaired-repeated-containment": "comparison fails: duplicate collector rows",
    "unpaired-two-feature-containment": "comparison fails: duplicate collector rows",
}
# Table 2 family label -> run_fifth_evaluation.py family name; sizes are object counts.
TABLE2_FAMILIES = {"Containment star": "containment-inheritance",
                   "Train projection": "train-projection",
                   "Containment chain": "recursive-containment"}


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def tabular_rows(text: str, start: str):
    """Rows of the first tabular after `start`, split on '&' with LaTeX math removed."""
    body = text[text.index(start):]
    body = body[body.index(r"\begin{tabular}"):body.index(r"\end{tabular}")]
    rows = []
    for line in body.splitlines():
        line = line.strip()
        if "&" in line and line.endswith("\\\\"):
            rows.append([cell.strip().replace("$", "") for cell in line[:-2].split("&")])
    return rows


def paper_table1():
    rows = tabular_rows(EVALUATION_TEX.read_text(encoding="utf-8"), r"\textbf{(a) Validation decisions}")
    return {label: tuple(cells) for label, *cells in rows[1:]}


def paper_table2():
    rows = tabular_rows(TIMES_TEX.read_text(encoding="utf-8"), r"\label{tab:validation-times}")
    return {(label, int(objects)): {"rows": int(n_rows), "emf": emf, "vlmof": vlmof}
            for label, objects, n_rows, emf, vlmof in rows[1:]}


def decision(value) -> str:
    return {True: "Accept", False: "Reject", "accepted": "Accept", "rejected": "Reject"}.get(value, str(value))


def state_comparison(fixture) -> str:
    normalization = fixture["phases"].get("normalization", {})
    alignment = normalization.get("loaded_to_core")
    if not alignment:
        return f"not compared ({normalization.get('status')})"
    kinds = {problem.get("kind") for problem in alignment.get("problems", [])}
    if alignment.get("lossless"):
        return "match"
    if kinds & {"duplicate-loaded-observation-key", "duplicate-loaded-identity"}:
        return "comparison fails: duplicate collector rows"
    mismatches = alignment.get("mismatches", [])
    presence = [m for m in mismatches if sorted(len(m.get(k) or []) for k in ("loaded_values", "core_values")) == [0, 1]]
    if mismatches and not kinds and len(presence) == len(mismatches) and not alignment.get("object_classifier_mismatches"):
        return f"{len(presence)} scalar-presence differences"
    return f"other mismatch ({len(mismatches)} values, problems {sorted(kinds)})"


def table1(args) -> int:
    paper = paper_table1()
    if set(paper) != set(TABLE1_FIXTURES):
        print(f"paper Table 1 rows changed; update TABLE1_FIXTURES: {sorted(set(paper) ^ set(TABLE1_FIXTURES))}")
        return 2
    row_of = {fixture: label for label, ids in TABLE1_FIXTURES.items() for fixture in ids}
    observed, failures, report = {}, 0, {"sources": [], "fixtures": [], "rows": []}
    for path in args.results:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        report["sources"].append({"path": str(path), "sha256": sha256(Path(path)),
                                  "all_expected": data.get("all_expected"),
                                  "source_bytes_unchanged": data.get("source_bytes_unchanged")})
        for fixture in data.get("fixtures", []):
            emf = fixture["phases"]["emf_validation"].get("report") or {}
            observed[fixture["id"]] = (decision(emf.get("schema_accepted")),
                                       decision(emf.get("instance_accepted")),
                                       decision(fixture["phases"].get("vlmof_validation", {}).get("status")),
                                       state_comparison(fixture))
    print("| Fixture | Table 1 row | EMF schema | EMF instance | VL-MOF | State after loading | Agrees |")
    print("|---|---|---|---|---|---|---|")
    for fixture, values in sorted(observed.items()):
        label = row_of.get(fixture)
        if label is None:
            agrees = "not a Table 1 case"
        else:
            expected = paper[label] + (TABLE1_STATE.get(fixture, "match"),)
            agrees = "yes" if values == expected else f"NO (paper: {', '.join(expected)})"
            failures += values != expected
        print(f"| {fixture} | {label or '-'} | {' | '.join(values)} | {agrees} |")
        report["fixtures"].append({"id": fixture, "row": label, "observed": values, "agrees": agrees})
    print()
    for label, ids in TABLE1_FIXTURES.items():
        present = [i for i in ids if i in observed]
        status = ("not in these results" if not present else
                  f"{len(present)}/{len(ids)} fixtures present")
        print(f"- {label}: paper {', '.join(paper[label])}; {status}")
        report["rows"].append({"row": label, "paper": paper[label], "fixtures": ids, "present": present})
    for source in report["sources"]:
        print(f"- {source['path']}: all_expected={source['all_expected']}, "
              f"source_bytes_unchanged={source['source_bytes_unchanged']}")
    if args.json:
        Path(args.json).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"\n{failures} fixture(s) disagree with the printed Table 1.")
    return 1 if failures else 0


def process_median(tool_report, key, policy):
    samples = (tool_report or {}).get(key)
    if not valid_samples(samples, policy["warmups"], policy["repetitions"]):
        return None
    return statistics.median(row["nanoseconds"] / 1e6 for row in samples if row["warmup"] is False)


def table2(args) -> int:
    run = Path(args.run_dir).resolve()
    aggregate = json.loads((run / "results.json").read_text(encoding="utf-8"))
    policy = aggregate["policy"]
    paper = paper_table2()
    cells = {}
    for trial in aggregate.get("trials", []):
        family, size = trial["family"], trial["size"]
        cell = cells.setdefault((family, size), {"objects": None, "rows": None, "trials": 0, "orders": set(),
                                                 "emf": [], "vlmof": [], "vlmof_timeouts": 0, "paired": 0})
        cell["trials"] += 1
        cell["orders"].add(trial["order"])
        worker = run / "timing" / f"trial-{trial['trial']}" / f"{family}-{size}" / "results.json"
        if not worker.is_file():
            continue
        fixture = json.loads(worker.read_text(encoding="utf-8"))["fixtures"][0]
        alignment = fixture["phases"]["normalization"].get("loaded_to_core") or {}
        cell["objects"], cell["rows"] = alignment.get("core_object_count"), alignment.get("core_observation_count")
        timing = fixture.get("timing", {})
        emf = process_median((timing.get("emf") or {}).get("report"), "samples", policy)
        lean_report = (timing.get("lean") or {}).get("report")
        vlmof = process_median(lean_report, "schemaAndSnapshot", policy)
        if vlmof is not None and process_median(lean_report, "schema", policy) is None:
            vlmof = None
        if emf is not None:
            cell["emf"].append(emf)
        if vlmof is not None:
            cell["vlmof"].append(vlmof)
        elif "timed out" in str(((timing.get("lean") or {}).get("record") or {}).get("error", "")):
            cell["vlmof_timeouts"] += 1
        cell["paired"] += timing.get("complete") is True

    def summary(values, trials, timeouts=0):
        if values and len(values) == trials:
            return f"{statistics.median(values):.3f}"
        if timeouts == trials:
            return "timeout"
        return f"incomplete {len(values)}/{trials}"

    problems, rows = [], []
    print(f"Policy: {policy['trials']} process trials, {policy['warmups']} warmups, "
          f"{policy['repetitions']} retained repetitions per process.")
    print("| Family/shape | Objects | Rows | EMF | VL-MOF | Paired complete | Paper EMF | Paper VL-MOF |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    for (label, objects), printed in paper.items():
        key = (TABLE2_FAMILIES[label], objects)
        cell = cells.get(key)
        if cell is None:
            problems.append(f"no trials for {key}")
            continue
        emf = summary(cell["emf"], cell["trials"])
        vlmof = summary(cell["vlmof"], cell["trials"], cell["vlmof_timeouts"])
        if (cell["objects"], cell["rows"]) != (objects, printed["rows"]):
            problems.append(f"{key}: objects/rows {cell['objects']}/{cell['rows']} differ from paper")
        if args.exact and (emf, vlmof) != (printed["emf"], printed["vlmof"]):
            problems.append(f"{key}: {emf}/{vlmof} differ from the printed {printed['emf']}/{printed['vlmof']}")
        if cell["trials"] != policy["trials"] or len(cell["orders"]) < min(2, policy["trials"]):
            problems.append(f"{key}: {cell['trials']} trials, orders {sorted(cell['orders'])}")
        print(f"| {label} | {cell['objects']} | {cell['rows']} | {emf} | {vlmof} | "
              f"{cell['paired']}/{cell['trials']} | {printed['emf']} | {printed['vlmof']} |")
        rows.append({"family": label, "fixture": f"{key[0]}-{key[1]}", "objects": cell["objects"],
                     "rows": cell["rows"], "emf_ms": emf, "vlmof_ms": vlmof,
                     "emf_process_medians_ms": cell["emf"], "vlmof_process_medians_ms": cell["vlmof"],
                     "paired_complete": cell["paired"], "trials": cell["trials"],
                     "paper_emf_ms": printed["emf"], "paper_vlmof_ms": printed["vlmof"]})
    paired = sum(c["paired"] for c in cells.values())
    total = sum(c["trials"] for c in cells.values())
    print(f"\n{paired} of {total} paired timing trials complete (paper: 40 of 45).")
    print("Times in a fresh run are new observations; only objects, rows and the schedule must match.")
    for problem in problems:
        print(f"PROBLEM: {problem}")
    if args.json:
        Path(args.json).write_text(json.dumps({"run": str(run), "policy": policy, "rows": rows,
                                               "paired_complete": paired, "trials": total,
                                               "problems": problems}, indent=2) + "\n", encoding="utf-8")
    return 1 if problems else 0


def tree(directory: Path):
    files = sorted(p for p in directory.rglob("*") if p.is_file() and not p.is_symlink())
    lines = [f"{sha256(p)}  {p.relative_to(directory).as_posix()}\n" for p in files]
    return {"files": len(files), "bytes": sum(p.stat().st_size for p in files),
            "tree_sha256": hashlib.sha256("".join(lines).encode()).hexdigest()}


def companion(args) -> int:
    manifest = json.loads(COMPANION.read_text(encoding="utf-8"))
    root, failures = Path(args.root).resolve(), 0
    for item in manifest["collections"]:
        directory = root / (item["author_workspace_path"] if args.workspace_layout else item["name"])
        if not directory.is_dir():
            print(f"MISSING  {item['name']}: {directory}")
            failures += 1
            continue
        observed = tree(directory)
        same = all(observed[k] == item[k] for k in ("files", "bytes", "tree_sha256"))
        bad_keys = [k["path"] for k in item["key_files"]
                    if not (directory / k["path"]).is_file() or sha256(directory / k["path"]) != k["sha256"]]
        failures += (not same) or bool(bad_keys)
        print(f"{'OK      ' if same and not bad_keys else 'DIFFERS '}{item['name']}: "
              f"{observed['files']} files, {observed['bytes']} bytes"
              + (f"; key files differing: {bad_keys}" if bad_keys else ""))
    print(f"{failures} collection(s) missing or different.")
    return 1 if failures else 0


# Author-workspace locations (relative to the workspace root that contains misc/ and
# repo/), the claims each collection supports, and the files a reader should open.
COLLECTIONS = [
    ("multifamily-evaluation-03", "misc/fift-review/evidence/multifamily-evaluation-03",
     "Table 1 authored rows and Train explicit-defaults row (correctness/); Table 2 (timing/)",
     {"results.json": "timing campaign index: policy, input hashes, 45 trial launches",
      "correctness/results.json": "Table 1 decisions and state comparisons for 18 fixtures"}),
    ("public-raw-alignment-01", "misc/fift-review/evidence/public-raw-alignment-01",
     "Table 1 row 'Train with original omissions'; 754 objects / 3,378 rows; full Train DSL input",
     {"results.json": "EMF and VL-MOF decisions and lossless state comparison",
      "normalized/public-train-raw-batch-1-profile.e1.json": "Core JSON rendered as examples/train/full-v1-batch-1.dsl"}),
    ("public-evaluation-01", "misc/fift-review/evidence/public-evaluation-01",
     "run_public.py evidence (six adapted Train round trips, controls, EMF Compare rejection); "
     "fixture manifest and profile Ecore used by public-raw-alignment-01",
     {"results.json": "public runner index", "raw-batch-1-profile.fixture.json":
      "manifest of the original-omissions comparison", "artifacts/railway.profile.ecore": "adapted Train metamodel"}),
    ("third-review-public", "misc/third_review/development/delivery/VL-MOF-artifact/evidence/public",
     "adapted Train inputs named by experiments/cases/emf-validation/train-batch-1-profile.fixture.json",
     {"results.json": "earlier public runner index",
      "artifacts/railway.profile.ecore": "adapted Train metamodel",
      "cases/railway-batch-1/adapted.xmi": "batch-1 with twelve materialized FAILURE defaults",
      "cases/railway-batch-1/adaptation.manifest.json": "list of the inserted defaults"}),
    ("reproduction-results-07", "misc/07th-review/reproduction-results",
     "recomputation of Table 2 from retained samples and the full Train DSL check (no new timing)",
     {"results.json": "commands and outcomes of the recomputation", "timing-summary.json": "per-trial statistics"}),
]


def manifest(args) -> int:
    workspace, output = Path(args.workspace).resolve(), Path(args.output)
    collections = []
    for name, relative, supports, keys in COLLECTIONS:
        directory = workspace / relative
        collections.append({"name": name, "author_workspace_path": relative, "supports": supports,
                            **tree(directory),
                            "key_files": [{"path": path, "role": role, "bytes": (directory / path).stat().st_size,
                                           "sha256": sha256(directory / path)} for path, role in keys.items()]})
    previous = json.loads(output.read_text(encoding="utf-8")) if output.exists() else {}
    data = {"format": "vlmof-companion-evidence-1",
            "tree_sha256": "SHA-256 of the lines '<sha256>  <relative path>\\n' for every regular file, sorted by path",
            "collections": collections,
            **{k: previous[k] for k in ("not_redistributed", "notes") if k in previous}}
    output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    one = commands.add_parser("table1", help="Table 1 rows from run_emf_validation.py results.json files")
    one.add_argument("results", nargs="+")
    one.add_argument("--json")
    two = commands.add_parser("table2", help="Table 2 from a run_fifth_evaluation.py output directory")
    two.add_argument("run_dir")
    two.add_argument("--json")
    two.add_argument("--exact", action="store_true",
                     help="also require the printed times (for retained historical evidence only)")
    check = commands.add_parser("companion", help="verify retained evidence against companion-evidence.json")
    check.add_argument("root")
    check.add_argument("--workspace-layout", action="store_true",
                       help="ROOT is the author workspace (misc/...), not a companion archive root")
    make = commands.add_parser("manifest", help="regenerate companion-evidence.json (maintainers)")
    make.add_argument("workspace")
    make.add_argument("output", nargs="?", default=str(COMPANION))
    args = parser.parse_args()
    return {"table1": table1, "table2": table2, "companion": companion, "manifest": manifest}[args.command](args)


if __name__ == "__main__":
    raise SystemExit(main())
