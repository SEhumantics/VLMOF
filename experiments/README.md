# Evaluation inputs, provenance and protocol

This guide describes what the evaluation runs on, how each input was obtained or
changed, and how validation decisions, loaded states and times are measured.
Commands are in the [reproduction guide](../REPRODUCING.md). The
[paper map](../docs/paper-map.md) traces each claim and table row to this material.

## Files

| Paper material | Location |
|---|---|
| Running example `M_T` and Section 3 counterexamples | [`examples/running-example/`](../examples/running-example/) |
| Complete Train notation (754 objects) | [`examples/train/full-v1-batch-1.dsl`](../examples/train/full-v1-batch-1.dsl) |
| Small Train projections | [`examples/train/`](../examples/train/) |
| EMF comparison and timing fixtures (`.ecore`, `.xmi`, `.fixture.json`) | [`cases/emf-validation/`](cases/emf-validation/) |
| Synthetic workload generator | [`generate_scaling_cases.py`](generate_scaling_cases.py) |
| EMF comparison runner (Table 1) | [`run_emf_validation.py`](run_emf_validation.py) |
| Timing runner (Table 2) | [`run_fifth_evaluation.py`](run_fifth_evaluation.py), [`ValidationBench.lean`](ValidationBench.lean), `bridge/…/EmfValidationHarness.java` |
| Public import and round-trip runner | [`run_public.py`](run_public.py) |
| Public input pins and acquisition | [`cases/README.md`](cases/README.md), [`cases/fetch-public-cases.sh`](cases/fetch-public-cases.sh) |
| Full Train equality and edit check | [`TrainWalkthrough.lean`](TrainWalkthrough.lean), [`docs/train-walkthrough.md`](../docs/train-walkthrough.md) |
| Authored CLI cases and proof client | [`run.py`](run.py), [`ProofClient.lean`](ProofClient.lean) |
| Paper-to-Lean names | [`PaperMap.lean`](PaperMap.lean) |
| Wrapper, table recomputation, evidence manifest | [`reproduce.py`](reproduce.py), [`evidence.py`](evidence.py), [`companion-evidence.json`](companion-evidence.json) |

## Inputs and provenance

### Authored fixtures

The EMF comparison fixtures were written for this study to isolate one behaviour
each. [`cases/emf-validation/README.md`](cases/emf-validation/README.md) explains
them. A manifest names its Ecore and XMI files, the expected outcome where the
semantics has been reviewed, and whether the case is eligible for timing. Cases
without an expectation are separators: they record a difference rather than
score it. `train-route-switch` realizes the authored Train projection
[`examples/train/route-switch.dsl`](../examples/train/route-switch.dsl) in
Ecore/XMI; it is not upstream Train data.

### Synthetic timing workloads

`generate_scaling_cases.py` deterministically writes the nine timed fixtures, and
records its parameters in each manifest's `generator` field:

- **Containment star**: one container with 10, 100 or 500 inherited-feature children and ordered value lists.
- **Train projection**: 2, 20 or 100 groups shaped like `M_T` over six Train classes.
- **Containment chain**: each node contained in its predecessor, to depth 10, 100 or 500.

The timing runner regenerates these into its output directory and stops unless the
result is byte-identical to the committed files. These workloads are **not** the
Train Benchmark's query workload: no benchmark query, injection or repair runs. The
public 754-object Train snapshot is **not** timed. Its fixtures are
`timing_eligible: false`, and Table 2 contains only the nine synthetic cells.

### Train Benchmark inputs and adaptations

Source: <https://github.com/FTSRG/trainbenchmark>, tag `v1.0`, commit
`6490047d7449f9a4b66cec032b9377bfc06a54d2`, EPL-1.0. Two files are evaluated:
`trainbenchmark-format-emf-model/src/railway.xcore` and `models/railway-*.xmi`.
The snapshots are generated benchmark models, not operational railway data. The
Xcore and batch-1 hashes are verified on fetch.
[`cases/README.md`](cases/README.md) lists the source inventory; the six-snapshot
counts are reproduced by `inventory_train_snapshots.py`.

1. **Metamodel compilation.** `XcoreToEcore` (Xcore 1.28.0) compiles the Xcore to `railway.generated.ecore`. This unadapted Ecore is imported as a control and is expected to be `unsupported`: it keeps a generator annotation and maps three attributes to `EJavaObject`.
2. **Metamodel adaptation.** `StripEcoreAnnotations` writes the separate `railway.profile.ecore` and a manifest of the qualified changes and hashes (`railway.profile.manifest.json`). It removes exactly one generator annotation, and maps `RailwayElement.id` and `Segment.length` to `EInt` and `Route.active` to `EBoolean`. Nothing else changes. The lower bound zero of `route`, `target`, `entry` and `exit` is v1.0's own. The published article's diagram shows these ends as required; the paper's Figure 1 follows v1.0.
3. **Untouched omissions.** Batch-1 XMI, unchanged, is imported against the profile Ecore. Six `SwitchPosition.position` and six `Switch.currentPosition` values are omitted in the source. They become empty rows `⟨⟩` in Core and are unset (`eIsSet = false`) in EMF. The states align (754 objects, 3,378 rows), and both tools accept, because the lower bounds are zero. This is the row "Train with original omissions".
4. **Explicitly materialized enum defaults.** `bridge/scripts/adapt_train_defaults.py` writes a separate XMI copy that writes each omitted enum value explicitly as the first literal, `FAILURE`. It lists every insertion with hashes in `adaptation.manifest.json`: 12, 58, 21, 76, 31 and 58 insertions for batch-1, batch-2, inject-1, inject-2, repair-1 and repair-2. Core keeps the explicit value as a one-element row. EMF's `eIsSet` reports a value equal to the default as unset, so batch-1 shows 12 presence differences while both validators accept. This is the row "Train with explicit defaults". Materialization changes the recorded meaning. It is not needed for conformance.

`run_public.py` runs all six adapted snapshots through import, Core check, fresh
export, reimport, identity-mapped comparison and second Core check. These show that
the adapted inputs are accepted. They do not show that the raw resources conform
unchanged, or that default/unset behaviour matches EMF in general.

### EMF Compare

Source: <https://github.com/eclipse-emf-compare/emf-compare>, tag `3.3.28`, commit
`9f25a964c1be423373587d8063a5b132714ebeae`, EPL-1.0. The evaluated file is
`plugins/org.eclipse.emf.compare/model/compare.ecore`. The model has:

- 12 operations;
- derived and transient features;
- Java-backed data types such as `EJavaObject` and `IEqualityHelper`;
- references to Ecore's reflective types.

All of these lie outside the structural subset. The importer rejects the original
model for its operations, before any Core document exists. The public runner
expects and records that outcome as `unsupported`. No projection of EMF Compare
was evaluated, and none should be presented as EMF Compare support.

## Protocol

### EMF comparison (Table 1)

The Java harness uses EMF Ecore/XMI 2.39.0 and Common 2.42.0 on Java 21. For each
fixture it creates a manifest-closed resource set and loads the Ecore and XMI files.
It also creates an isolated `EValidatorRegistryImpl` that registers `EcoreValidator`
for the Ecore package; dynamic instance packages fall back to `EObjectValidator`.
A fresh `Diagnostician` then validates each Ecore root (**schema** decision) and
each XMI root (**instance** decision) in separate calls. The harness uses no
generated validators, no OCL or validation delegates, and not the global
`Diagnostician.INSTANCE`.

VL-MOF receives the same files through the bridge import (`EmfInterchange`). It
checks the resulting Core document with `vlmof check-json`: one **combined**
decision that includes `W(S)`. See [`docs/validation.md`](../docs/validation.md).

The loaded-state comparison runs in `compare_loaded_to_core`, in
`run_emf_validation.py`. For every loaded object and feature, the harness records
the feature's values when `eIsSet` holds and an empty list otherwise; it does not
call `eGet` unconditionally. The runner builds bijections between Core identities
and native URIs for objects, classes, properties, enumerations and literals. It
then compares:

- classifiers;
- declaration inventories: property owners, ordering and types, and literal owners;
- every observation row: ordered features as sequences, unordered ones as sorted multisets.

Missing or duplicate rows and non-bijective identity maps count as problems, never
as empty rows. The result is `lossless` only without mismatches or problems.
Repeated traversal of a contained object by the collector yields duplicate rows,
so the two unpaired-containment fixtures fail the comparison.

### Timing (Table 2)

- **Eligibility.** A fixture is timed only if its manifest says `timing_eligible`, both tools accept it, and its loaded-state comparison is lossless. The nine synthetic fixtures qualify. The Train and separator fixtures are not timed.
- **Boundary.** Both tools time preloaded, combined schema and instance validation.
  - EMF (`EmfValidationHarness warm-validate`) first loads the resources and produces the untimed diagnostic report. It then times each validation of all roots with `System.nanoTime`, returning only a Boolean.
  - VL-MOF (`validationBench`) reads and decodes the Core JSON once. It then times each non-inlined `checkSnapshot` call on the stored document with `IO.monoNanosNow`. A separate schema-only series (`checkSchema`) runs first in the same process; Table 2 does not use it.
  - Loading, JSON parsing, serialization, diagnostics and process start are outside the clock. Instance-only time is not measured.
- **Independent processes.** A trial of one workload is a new `run_emf_validation.py --measure` process. It repeats the correctness steps for that fixture, then starts one EMF process (Maven `exec:java`, a new JVM) and one Lean process. Each workload gets five trials.
- **Warmups and repetitions.** Each process runs 10 warmup and 30 retained iterations. Samples carry a `warmup` flag, and only the 30 retained ones are summarized.
- **Counterbalancing.** Odd trials visit the nine workloads in order and even trials in reverse. Within a workload, EMF runs first when the workload's fixed index plus the trial number is odd. Over five trials each workload therefore gets both tool orders, split 3 and 2.
- **Aggregation.** Take the median of each process's 30 retained samples, then the median of the five process medians. A cell needs all five processes of that tool to complete.
- **Correctness gate.** Before any trial, the timing runner reruns the EMF comparison on the local fixtures. Timing starts only if every scored expectation holds.
- **Timeout.** Every worker process has a 120-second limit, and a process that exceeds it is killed and leaves no samples. For VL-MOF, the limit covers the file read, decoding, 40 schema-only and 40 combined iterations, and process overhead. A "timeout" cell is therefore a batch limit, not a single-validation time. In the paper's run, all five VL-MOF processes for the 501-deep chain timed out: 40 of 45 paired trials completed.

Ten warmups do not establish JIT stabilization, and the times hold only for the
machine, versions and state recorded with them.

## Outcomes and failures

| Runner | Result classes | Exit status |
|---|---|---|
| `run.py` | `accepted`, `rejected` (invalid, malformed or binding failure; phase kept), `unsupported`, `not-run` (missing executable), `execution-failure` | 0 only if every case matches its expectation |
| `run_emf_validation.py` | Per fixture: EMF `accepted`/`rejected`/`execution-failure`; normalization `accepted`/`normalization-loss`/`execution-failure`; VL-MOF `accepted`/`rejected`/`malformed`/`unsupported`/`execution-failure`/`not-run`. `matches_expected` is `null` for unscored separators. | 0 only if source bytes are unchanged, every scored fixture matches, and every requested timing is complete |
| `run_public.py` | `accepted`, `rejected`, `unsupported`, `not-run`, `execution-failure` | 0 only if all six adapted snapshots and the raw control are accepted, both unsupported controls give the expected diagnostic, and the raw inputs are unchanged |
| `run_fifth_evaluation.py` | Per trial: exit code, timeout and worker summary | The correctness exit code if the gate fails; otherwise 0 only if every trial succeeds. **Exit 1 with five incomplete deep-chain trials is the paper's outcome.** |
| `reproduce.py` | Per step: `passed`, `failed`, `differs` (bytes differ from retained evidence), `not-run` (an earlier step produced no input) | 0 only if every step passed |

These classes mean different things:

- A **rejection** is a validator's answer about the model.
- An **execution failure** says nothing about the model: the tool did not run, crashed, timed out or produced an unreadable report.
- An **unexpected** result is a discrepancy to report with its logs. It does not change the historical tables.
- An **incomplete** timing run keeps every finished trial. `evidence.py table2` marks its cells `incomplete k/5`, or `timeout` when all five processes timed out.

Each runner writes its structured record to `results.json` in its output directory:

| Runner | Other contents of the output directory |
|---|---|
| `run.py` | the authored inputs in `inputs/` |
| `run_emf_validation.py` | `commands/NNN-*.stdout` and `.stderr`, digests recorded; `normalized/<fixture>.e1.json` |
| `run_public.py` | `commands/`, `artifacts/` (generated and profile Ecore), `cases/<snapshot>/` (adapted XMI, manifests, checks, exports), `controls/` |
| `run_fifth_evaluation.py` | `correctness/` (a full EMF comparison run), `generated-fixtures/`, one `run_emf_validation.py` directory per trial and workload in `timing/trial-k/<workload>/`, and launcher logs |
| `reproduce.py` | `reproduce.json`, `SUMMARY.md`, `logs/`, and the runner directories above |

## Retained evidence

The printed Tables 1 and 2 were computed from evidence recorded on 15 Sep 2026
that is not in this repository. [`companion-evidence.json`](companion-evidence.json)
lists each collection, what it supports, its file count, size and tree digest,
and the hashes of the files a reader should open:

| Collection | Supports |
|---|---|
| `multifamily-evaluation-03` | Table 1, except the original-omissions row (`correctness/`); Table 2 (`timing/`) |
| `public-raw-alignment-01` | Table 1 "Train with original omissions"; the Core document behind `full-v1-batch-1.dsl` |
| `public-evaluation-01` | public runner evidence; the manifest and profile Ecore of the original-omissions comparison |
| `third-review-public` | the adapted Train inputs named by `cases/emf-validation/train-batch-1-profile.fixture.json` |
| `reproduction-results-07` | a recomputation of Table 2 from the raw samples; no new timing |

Verify a copy with `python3 experiments/evidence.py companion ROOT`. In the
author's workspace, these directories sit under `misc/`, and the manifest records
their exact locations. A source checkout alone does not contain this evidence,
and a fresh run creates new evidence. A fresh run must not be presented as a
recovery of the historical measurements.
