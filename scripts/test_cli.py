"""Process-level checks of the published JSON command, with authored wire inputs."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake' / 'build' / 'bin' / 'vlmof'


def document():
    return {
        'version': 'vlmof-e1-1', 'provenance': {'kind': 'authored-cli-test'},
        'schema': {
            'packages': [],
            'classes': [{'id': 0, 'name': 'C', 'package': None, 'abstract': False, 'supers': []}],
            'properties': [{'id': 0, 'name': 'active', 'owner': {'tag': 'class', 'id': 0},
                'type': {'tag': 'boolean'}, 'multiplicity': {'lower': 0,
                    'upper': {'tag': 'finite', 'value': 1}, 'ordered': False, 'unique': True},
                'aggregation': 'none', 'idProperty': False}],
            'associations': [], 'enumerations': [], 'literals': []},
        'snapshot': {'objects': [{'id': 0, 'classifier': 0}],
            'observations': [{'object': 0, 'property': 0,
                'occurrences': [{'tag': 'boolean', 'value': False}]}]}}


class CommandTests(unittest.TestCase):
    def invoke(self, payload, expected_code, expected_status):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input.json'
            path.write_text(payload if isinstance(payload, str) else json.dumps(payload), encoding='utf-8')
            result = subprocess.run([str(BINARY), 'check-json', str(path)], capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, expected_code, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report['status'], expected_status)
        self.assertEqual(result.stderr, '')
        return report

    def test_boolean_false_and_optional_empty(self):
        value = document()
        self.invoke(value, 0, 'accepted')
        value['snapshot']['observations'][0]['occurrences'] = []
        self.invoke(value, 0, 'accepted')
        value['snapshot']['observations'] = []
        report = self.invoke(value, 1, 'invalid')
        self.assertIn({'phase': 'snapshot', 'field': 'observations exact'}, report['diagnostics'])

    def test_repeated_integer_occurrences_are_not_dropped(self):
        value = document()
        prop = value['schema']['properties'][0]
        prop['type'] = {'tag': 'integer'}
        prop['multiplicity'] = {'lower': 2, 'upper': {'tag': 'finite', 'value': 2}, 'ordered': True, 'unique': False}
        value['snapshot']['observations'][0]['occurrences'] = [{'tag': 'integer', 'value': 0}] * 2
        self.invoke(value, 0, 'accepted')
        prop['multiplicity']['unique'] = True
        report = self.invoke(value, 1, 'invalid')
        self.assertIn({'phase': 'snapshot', 'field': 'unique occurrences'}, report['diagnostics'])

    def test_duplicate_key_and_wrong_type(self):
        value = document()
        value['snapshot']['observations'].append(copy.deepcopy(value['snapshot']['observations'][0]))
        report = self.invoke(value, 1, 'invalid')
        self.assertIn({'phase': 'snapshot', 'field': 'unique observation keys'}, report['diagnostics'])
        value = document()
        value['snapshot']['observations'][0]['occurrences'] = [{'tag': 'integer', 'value': 0}]
        report = self.invoke(value, 1, 'invalid')
        self.assertIn({'phase': 'snapshot', 'field': 'values typed'}, report['diagnostics'])

    def test_malformed_and_unsupported_are_separate(self):
        self.invoke('{', 2, 'malformed')
        self.invoke({}, 2, 'malformed')
        self.invoke({'version': 'future'}, 3, 'unsupported')
        value = document()
        value['snapshot']['objects'][0]['id'] = -1
        self.invoke(value, 2, 'malformed')
        value = document()
        value['schema']['properties'][0]['multiplicity']['upper']['value'] = 0
        self.invoke(value, 1, 'invalid')

    def test_missing_file_and_usage(self):
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([str(BINARY), 'check-json', str(Path(directory) / 'absent.json')], capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 4)
        self.assertEqual(json.loads(result.stdout)['status'], 'io-error')
        result = subprocess.run([str(BINARY)], capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(json.loads(result.stdout)['status'], 'usage')


if __name__ == '__main__':
    unittest.main()
