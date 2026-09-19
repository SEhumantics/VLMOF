import argparse
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


runner = load("emf_validation_runner_selection", "experiments/run_emf_validation.py")
evidence = load("evidence_tool", "experiments/evidence.py")
reproduce = load("reproduce_wrapper", "experiments/reproduce.py")


class FixtureSelectionTests(unittest.TestCase):
    def test_default_selection_excludes_manifests_with_inputs_outside_the_repository(self):
        selected, excluded = runner.select_manifests(None)
        names = {path.name for path in selected}
        self.assertIn("tiny-valid.fixture.json", names)
        self.assertNotIn("train-batch-1-profile.fixture.json", names)
        self.assertEqual(["train-batch-1-profile.fixture.json"], [Path(row["manifest"]).name for row in excluded])

    def test_inputs_resolve_lexically_like_the_java_harness(self):
        with tempfile.TemporaryDirectory() as temporary:
            real = Path(temporary) / "real"
            real.mkdir()
            (Path(temporary) / "link").symlink_to(real)
            manifest = Path(temporary) / "cases" / "x.fixture.json"
            self.assertEqual(Path(temporary) / "link" / "a.ecore",
                             runner.input_path(manifest, "../link/sub/../a.ecore"))

    def test_missing_explicit_input_stops_before_any_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            manifest = Path(temporary) / "gone.fixture.json"
            manifest.write_text(json.dumps({"id": "gone", "ecore": ["gone.ecore"], "xmi": ["gone.xmi"]}))
            with self.assertRaises(SystemExit) as stop:
                runner.select_manifests([manifest])
            self.assertIn("nothing was run", str(stop.exception))


class PaperTableTests(unittest.TestCase):
    def test_paper_tables_are_parsed_and_mapped(self):
        self.assertEqual(set(evidence.TABLE1_FIXTURES), set(evidence.paper_table1()))
        self.assertEqual(("Accept", "Reject", "Reject"), evidence.paper_table1()["Missing required String"])
        rows = evidence.paper_table2()
        self.assertEqual(9, len(rows))
        self.assertEqual({"rows": 1503, "emf": "1.898", "vlmof": "timeout"}, rows[("Containment chain", 501)])
        self.assertEqual(11, len(evidence.TABLE1_FIXTURES["Aligned positives (11)"]))

    def test_state_comparison_distinguishes_presence_and_collector_failures(self):
        def fixture(**alignment):
            return {"phases": {"normalization": {"status": "x", "loaded_to_core": alignment}}}
        self.assertEqual("match", evidence.state_comparison(fixture(lossless=True)))
        presence = [{"loaded_values": [], "core_values": ["FAILURE"]}] * 12
        self.assertEqual("12 scalar-presence differences",
                         evidence.state_comparison(fixture(lossless=False, mismatches=presence, problems=[])))
        self.assertEqual("comparison fails: duplicate collector rows", evidence.state_comparison(
            fixture(lossless=False, mismatches=[], problems=[{"kind": "duplicate-loaded-observation-key"}])))
        self.assertTrue(evidence.state_comparison(fixture(lossless=False, mismatches=[
            {"loaded_values": ["1"], "core_values": ["2"]}], problems=[])).startswith("other mismatch"))

    def test_table2_takes_the_median_of_process_medians_and_reports_timeouts(self):
        def samples(values, warmups=1):
            return [{"index": i, "warmup": i < warmups, "nanoseconds": v, "accepted": True}
                    for i, v in enumerate([10**9] * warmups + values)]
        with tempfile.TemporaryDirectory() as temporary:
            run = Path(temporary)
            trials = []
            for trial, (emf_ms, lean_ms) in enumerate([(1, 4), (2, 5), (9, None)], start=1):
                trials.append({"trial": trial, "family": "recursive-containment", "size": 11,
                               "order": "emf-first" if trial % 2 else "vlmof-first"})
                lean = ({"report": {"schema": samples([1, 1]), "schemaAndSnapshot": samples([lean_ms * 10**6] * 2)},
                         "record": {"exit": 0}} if lean_ms else
                        {"report": None, "record": {"exit": None, "error": "timed out after 120 seconds"}})
                worker = {"fixtures": [{"phases": {"normalization": {"loaded_to_core": {
                    "core_object_count": 11, "core_observation_count": 33}}},
                    "timing": {"complete": lean_ms is not None, "emf": {"report": {"samples": samples([emf_ms * 10**6] * 2)}},
                               "lean": lean}}]}
                path = run / "timing" / f"trial-{trial}" / "recursive-containment-11" / "results.json"
                path.parent.mkdir(parents=True)
                path.write_text(json.dumps(worker))
            (run / "results.json").write_text(json.dumps({"policy": {"trials": 3, "warmups": 1, "repetitions": 2},
                                                          "trials": trials}))
            output = run / "table2.json"
            args = argparse.Namespace(run_dir=str(run), json=str(output), exact=False)
            with contextlib.redirect_stdout(io.StringIO()):
                evidence.table2(args)
            row = next(r for r in json.loads(output.read_text())["rows"] if r["fixture"] == "recursive-containment-11")
            self.assertEqual("2.000", row["emf_ms"])
            self.assertEqual("incomplete 2/3", row["vlmof_ms"])
            self.assertEqual(2, row["paired_complete"])


class WrapperPrerequisiteTests(unittest.TestCase):
    def arguments(self, output, phases):
        return argparse.Namespace(output=Path(output), train=None, emf_compare=None), phases

    def test_output_inside_repository_or_existing_is_refused(self):
        problems = reproduce.prerequisites(*self.arguments(ROOT / "evidence-here", ["sources"]))
        self.assertTrue(any("outside the repository" in p for p in problems))
        with tempfile.TemporaryDirectory() as temporary:
            problems = reproduce.prerequisites(*self.arguments(temporary, ["sources"]))
            self.assertTrue(any("must not exist" in p for p in problems))

    def test_timing_must_run_alone_and_public_needs_checkouts(self):
        with tempfile.TemporaryDirectory() as temporary:
            problems = reproduce.prerequisites(*self.arguments(Path(temporary) / "new", ["build", "timing"]))
            self.assertTrue(any("timing phase alone" in p for p in problems))
            problems = reproduce.prerequisites(*self.arguments(Path(temporary) / "new", ["public"]))
            self.assertTrue(any("--train" in p for p in problems))

    def test_maven_is_forced_offline(self):
        self.assertIn("--offline", reproduce.MAVEN_ARGS.split())


if __name__ == "__main__":
    unittest.main()
