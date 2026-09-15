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
        "classes": [{"id": 10, "identity": "c"}],
        "properties": [{"id": 2, "identity": "p"}],
        "enumerations": [],
        "literals": []}},
        "schema": {"classes": [{"id": 10}],
                   "properties": [{"id": 2, "owner": {"tag": "class", "id": 10},
                                   "type": {"tag": "string"},
                                   "multiplicity": {"ordered": True}}],
                   "enumerations": [], "literals": []},
        "snapshot": {"objects": [{"id": 1, "classifier": 10}], "observations": observations}}


class LoadedToCoreComparisonTests(unittest.TestCase):
    def loaded(self):
        return {"loaded_objects": [{"object_uri": "o", "class_uri": "c"}],
                "loaded_declarations": {
                    "classes": [{"class_uri": "c"}],
                    "properties": [{"feature_uri": "p", "owner_class_uri": "c",
                                    "type_uri": runner.ECORE_PRIMITIVE_URIS["string"], "ordered": True}],
                    "enumerations": [], "literals": []},
                "loaded_observations": [{"object_uri": "o", "feature_uri": "p",
                                         "is_set": False, "values": []}]}

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

    def test_zero_feature_object_still_participates_in_alignment(self):
        loaded = self.loaded()
        loaded["loaded_observations"] = []
        comparison = runner.compare_loaded_to_core(loaded, core([]))
        self.assertTrue(comparison["lossless"])
        self.assertEqual(comparison["loaded_object_count"], 1)

    def test_wrong_classifier_is_not_lossless(self):
        loaded = self.loaded()
        loaded["loaded_objects"][0]["class_uri"] = "other-class"
        comparison = runner.compare_loaded_to_core(loaded, core([]))
        self.assertFalse(comparison["lossless"])
        self.assertEqual(comparison["object_classifier_mismatches"][0]["core_class_uri"], "c")

    def test_missing_class_provenance_is_not_lossless(self):
        document = core([])
        document["provenance"]["identities"]["classes"] = []
        comparison = runner.compare_loaded_to_core(self.loaded(), document)
        self.assertFalse(comparison["lossless"])
        self.assertTrue(any(problem["kind"] == "provenance-store-coverage" for problem in comparison["problems"]))

    def test_duplicate_loaded_declaration_is_not_lossless(self):
        loaded = self.loaded()
        loaded["loaded_declarations"]["classes"].append({"class_uri": "c"})
        comparison = runner.compare_loaded_to_core(loaded, core([]))
        self.assertFalse(comparison["lossless"])
        self.assertTrue(any(problem["kind"] == "duplicate-loaded-identity" for problem in comparison["problems"]))

    def test_primitive_type_and_occurrence_tag_mismatch_cannot_hide_as_text(self):
        loaded = self.loaded()
        loaded["loaded_declarations"]["properties"][0]["type_uri"] = runner.ECORE_PRIMITIVE_URIS["integer"]
        loaded["loaded_observations"][0] = {
            "object_uri": "o", "feature_uri": "p", "is_set": True, "values": ["1"]}
        document = core([{"object": 1, "property": 2,
                          "occurrences": [{"tag": "integer", "value": 1}]}])
        comparison = runner.compare_loaded_to_core(loaded, document)
        self.assertFalse(comparison["lossless"])
        kinds = {problem["kind"] for problem in comparison["problems"]}
        self.assertIn("property-type-mismatch", kinds)
        self.assertIn("occurrence-tag-mismatch", kinds)
        self.assertEqual(comparison["mismatches"], [])

    def test_timing_requires_explicit_lossless_alignment(self):
        fixture = {"timing_eligible": True}
        self.assertFalse(runner.eligible_for_timing(fixture, "accepted", "accepted", {"lossless": False}))
        self.assertFalse(runner.eligible_for_timing(fixture, "accepted", "accepted", None))
        self.assertTrue(runner.eligible_for_timing(fixture, "accepted", "accepted", {"lossless": True}))

    def test_timing_completion_rejects_short_or_failed_samples(self):
        samples = [{"index": i, "warmup": i < 2, "nanoseconds": 1, "accepted": True}
                   for i in range(5)]
        record = {"exit": 0}
        emf = {"timing_boundary": "preloaded-schema-and-instance-validation",
               "all_timed_results_accepted": True, "samples": samples}
        self.assertTrue(runner.timing_complete(record, emf, "emf", 2, 3))
        emf["samples"] = samples[:-1]
        self.assertFalse(runner.timing_complete(record, emf, "emf", 2, 3))
        lean = {"schema": samples, "schemaAndSnapshot": samples}
        lean["schemaAndSnapshot"][4] = {**lean["schemaAndSnapshot"][4], "accepted": False}
        self.assertFalse(runner.timing_complete(record, lean, "lean", 2, 3))
