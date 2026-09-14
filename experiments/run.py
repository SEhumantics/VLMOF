#!/usr/bin/env python3
"""Record reproducible authored CLI cases and a proof-library client.

This initial suite does not stand in for the pending public-case EMF evaluation.
Run after make check. Output directories must be new to preserve previous evidence.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args, timeout=60):
    start = time.perf_counter()
    try:
        run = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        return {'command': [str(x) for x in args], 'exit': run.returncode,
                'stdout': run.stdout, 'stderr': run.stderr,
                'elapsed_seconds': time.perf_counter() - start}
    except (OSError, subprocess.TimeoutExpired) as error:
        return {'command': [str(x) for x in args], 'exit': None,
                'error': str(error), 'elapsed_seconds': time.perf_counter() - start}


def cases():
    base = json.loads((ROOT / 'examples/simple.json').read_text())
    yield 'explicit-false', 'check-json', base, 0, 'accepted', 'Boolean false is one value, not absence.'
    empty = copy.deepcopy(base)
    empty['snapshot']['observations'][0]['occurrences'] = []
    yield 'optional-empty', 'check-json', empty, 0, 'accepted', 'Lower zero permits an empty occurrence list.'
    missing = copy.deepcopy(base)
    missing['snapshot']['observations'] = []
    yield 'missing-observation', 'check-json', missing, 1, 'invalid', 'The profile requires an explicit row for each applicable property.'
    wrong = copy.deepcopy(base)
    wrong['snapshot']['observations'][0]['occurrences'] = [{'tag': 'integer', 'value': 0}]
    yield 'integer-is-not-boolean', 'check-json', wrong, 1, 'invalid', 'Integer zero is distinct from Boolean false.'
    duplicate = copy.deepcopy(base)
    duplicate['snapshot']['observations'] *= 2
    yield 'duplicate-observation', 'check-json', duplicate, 1, 'invalid', 'Observation keys are unique; duplicate rows are not merged.'
    yield 'future-wire-version', 'check-json', {'version': 'future'}, 3, 'unsupported', 'Unknown wire versions are outside the decoder domain.'
    yield 'malformed-json', 'check-json', '{', 2, 'malformed', 'Malformed syntax is reported before conformance checking.'
    dsl = (ROOT / 'examples/simple.dsl').read_text()
    yield 'dsl-authored', 'check-dsl', dsl, 0, 'accepted', 'Authored DSL preserves false and repeated integer occurrences.'
    yield 'dsl-unique-repetition', 'check-dsl', dsl.replace('ordered nonunique', 'ordered unique'), 1, 'invalid', 'Repeated equal values violate uniqueness when selected.'
    yield 'dsl-unknown-class', 'check-dsl', 'class C {} object x : Unknown {}', 2, 'binding-failure', 'Unresolved aliases fail binding, before Core validation.'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    inputs = output / 'inputs'
    inputs.mkdir()
    binary = ROOT / '.lake/build/bin/vlmof'
    revision = command(['git', 'rev-parse', 'HEAD'])
    dirty = command(['git', 'status', '--porcelain'])
    report = {
        'scope': 'Authored CLI cases and proof-client; public EMF evaluation pending.',
        'commit': revision.get('stdout', '').strip(),
        'dirty': bool(dirty.get('stdout', '').strip()),
        'platform': platform.platform(), 'python': sys.version,
        'lean': command(['lake', 'env', 'lean', '--version']),
        'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'runner_sha256': digest(Path(__file__)),
        'source_manifest_sha256': digest(ROOT / 'sources/manifest.json'),
        'expectation_basis_sha256': {str(p.relative_to(ROOT)): digest(p) for p in
            [ROOT / 'sources/PROFILE.md', ROOT / 'VLMOF/DSL.md']},
        'binary_sha256': digest(binary) if binary.exists() else None,
        'source_verification': command([sys.executable, 'scripts/sources.py', 'verify']),
        'timing_policy': 'Single invocations; durations are execution records, not benchmark claims.',
        'cases': []}
    statuses = {'accepted': 'accepted', 'unsupported': 'unsupported', 'invalid': 'rejected',
                'malformed': 'rejected', 'parse-malformed': 'rejected', 'binding-failure': 'rejected'}
    status_codes = {'accepted': 0, 'unsupported': 3, 'invalid': 1,
                    'malformed': 2, 'parse-malformed': 2, 'binding-failure': 2}
    for name, mode, payload, code, status, reason in cases():
        path = inputs / (name + ('.json' if mode == 'check-json' else '.dsl'))
        path.write_text(payload if isinstance(payload, str) else json.dumps(payload, indent=2), encoding='utf-8')
        row = {'id': name, 'origin': 'authored', 'input': str(path), 'input_sha256': digest(path),
               'expected': {'exit': code, 'status': status, 'reason': reason},
               'basis': 'sources/PROFILE.md and VLMOF/DSL.md', 'result': 'not-run'}
        if binary.exists():
            run = command([str(binary), mode, str(path)])
            row['execution'] = run
            try:
                parsed = json.loads(run.get('stdout', ''))
                row['observed'] = parsed
                row['result'] = statuses.get(parsed.get('status'), 'execution-failure')
                if run['exit'] != status_codes.get(parsed.get('status')) or run.get('stderr'):
                    row['result'] = 'execution-failure'
                row['matches_expectation'] = run['exit'] == code and parsed.get('status') == status and not run.get('stderr')
            except (ValueError, TypeError):
                row['result'] = 'execution-failure'
                row['matches_expectation'] = False
        else:
            row['matches_expectation'] = False
            row['reason_not_run'] = 'Build the vlmof executable before evaluation.'
        report['cases'].append(row)
    report['proof_client'] = command(['lake', 'env', 'lean', 'experiments/ProofClient.lean'])
    report['proof_client']['sha256'] = digest(ROOT / 'experiments/ProofClient.lean')
    report['all_expected'] = (report['source_verification']['exit'] == 0 and
        report['proof_client']['exit'] == 0 and all(c['matches_expectation'] for c in report['cases']))
    (output / 'results.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(f"{len(report['cases'])} cases; expectations matched: {report['all_expected']}; {output / 'results.json'}")
    return 0 if report['all_expected'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
