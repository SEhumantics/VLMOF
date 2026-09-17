# Evaluation files and reproduction

## Where the paper's inputs are

| Paper material | Location in this repository |
|---|---|
| Complete Train notation (754 objects) | [`examples/train/full-v1-batch-1.dsl`](../examples/train/full-v1-batch-1.dsl) |
| Small Train examples and negative edits | [`examples/train/`](../examples/train/) |
| Authored EMF correctness and scaling fixtures | [`cases/emf-validation/`](cases/emf-validation/) (`.ecore`, `.xmi`, `.fixture.json`) |
| Containment star | `cases/emf-validation/containment-inheritance-{11,101,501}.*` |
| Train projection | `cases/emf-validation/train-projection-{10,100,500}.*` (object counts) |
| Containment chain | `cases/emf-validation/recursive-containment-{11,101,501}.*` |
| Scaling input generator | [`generate_scaling_cases.py`](generate_scaling_cases.py) |
| EMF comparison runner | [`run_emf_validation.py`](run_emf_validation.py) |
| Independent-process timing runner | [`run_fifth_evaluation.py`](run_fifth_evaluation.py) |
| Public input pins, hashes and acquisition | [`cases/README.md`](cases/README.md), [`cases/fetch-public-cases.sh`](cases/fetch-public-cases.sh) |
| Public import/round-trip runner | [`README-public.md`](README-public.md), [`run_public.py`](run_public.py) |
| Full Train equality/negative-edit check | [`TrainWalkthrough.lean`](TrainWalkthrough.lean), [`docs/train-walkthrough.md`](../docs/train-walkthrough.md) |

Public upstream Xcore/XMI originals are fetched into a separate directory; they
are not vendored here. Generated outputs and historical timing logs are also
not checked into this source repository. A source checkout alone therefore does
not contain all evidence used for the printed tables.

In the author workspace `/home/xoruser/msc-5`, the retained evidence is:

- `misc/fift-review/evidence/multifamily-evaluation-03/`: original correctness
  observations and independent-process timing logs (`results.json`, `correctness/`,
  `timing/`). The spelling `fift-review` is the existing directory name.
- `misc/fift-review/evidence/public-raw-alignment-01/`: original-omission Train
  comparison, including its normalized Core document.
- `misc/third_review/development/delivery/VL-MOF-artifact/evidence/public/`:
  adapted public Ecore/XMI, adaptation manifests and public runner evidence.
- `misc/07th-review/reproduction-results/`: recomputed summaries and checks of
  retained evidence, not a new timing campaign.

These are local evidence locations, not portable paths or published download
links. `train-batch-1-profile.fixture.json` references this external workspace
layout and is not a standalone fixture. Distributing the source alone is
insufficient to reproduce the historical tables; the companion evidence must
be supplied with its manifest. Fresh runs produce new evidence and must not be
presented as recovery of the exact historical measured build.

## Reproduction records

After `make sources` and `make check`, run:

```sh
python3 experiments/run.py --output /absolute/new/result-directory
```

The directory must not already exist. The runner preserves authored inputs and
their hashes, repository commit and dirty status, executable hash, Lean/Python
environment, commands, exit codes, reports and observed outcomes. It also compiles
`ProofClient.lean`, which uses observation-key injectivity from the proof library
to show that two conforming observations for the same key have equal occurrence
lists. Its axiom report is preserved in the output.

The current ten cases cover JSON and DSL acceptance, absence versus false, typing,
duplicate keys, repetition/uniqueness, binding failure, malformed JSON and unsupported
wire versions. Expectations are explained per case and traced to the hashed profile
and grammar documents. Malformed and binding failures are classified as rejected
inputs, with their precise phase retained in the report. A missing executable is
`not-run`; timeouts, process failures and uninterpretable reports are execution failures.
An unexpected result remains visible and makes the runner fail.

This is the authored-case portion of evaluation. The [public runner](README-public.md)
records all six adapted Train round trips, raw-input controls, and EMF Compare
rejection with pinned inputs, exact commands, hashes and dependency versions.
Recorded durations are single operational measurements, not comparative benchmarks.
