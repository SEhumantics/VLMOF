import importlib.util
from pathlib import Path
import unittest


RUNNER = Path(__file__).resolve().parents[1] / "experiments" / "run_emf_validation.py"
SPEC = importlib.util.spec_from_file_location("emf_validation_runner", RUNNER)
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


def core(observations):
    return {"provenance": {"identities": {
        "objects": [{"id": 1, "identity": "o"}],
        "properties": [{"id": 2, "identity": "p"}],
        "literals": []}},
        "schema": {"properties": [{"id": 2, "multiplicity": {"ordered": True}}]},
        "snapshot": {"observations": observations}}


class LoadedToCoreComparisonTests(unittest.TestCase):
    def loaded(self):
        return {"loaded_observations": [{"object_uri": "o", "feature_uri": "p", "is_set": False, "values": []}]}

    def test_missing_core_row_is_not_empty_row(self):
        comparison = runner.compare_loaded_to_core(self.loaded(), core([]))
        self.assertFalse(comparison["lossless"])
        self.assertEqual(comparison["mismatches"][0]["core_values"], None)

    def test_duplicate_core_key_is_not_collapsed(self):
        observations = [{"object": 1, "property": 2, "occurrences": []},
                        {"object": 1, "property": 2, "occurrences": []}]
        comparison = runner.compare_loaded_to_core(self.loaded(), core(observations))
        self.assertFalse(comparison["lossless"])
        self.assertEqual(comparison["problems"][0]["kind"], "duplicate-core-observation-key")

    def test_non_bijective_provenance_is_not_collapsed(self):
        document = core([])
        document["provenance"]["identities"]["objects"].append({"id": 3, "identity": "o"})
        comparison = runner.compare_loaded_to_core(self.loaded(), document)
        self.assertFalse(comparison["lossless"])
        self.assertTrue(any(problem["kind"] == "duplicate-provenance-uri" for problem in comparison["problems"]))

    def test_timing_requires_explicit_lossless_alignment(self):
        fixture = {"timing_eligible": True}
        self.assertFalse(runner.eligible_for_timing(fixture, "accepted", "accepted", {"lossless": False}))
        self.assertFalse(runner.eligible_for_timing(fixture, "accepted", "accepted", None))
        self.assertTrue(runner.eligible_for_timing(fixture, "accepted", "accepted", {"lossless": True}))
