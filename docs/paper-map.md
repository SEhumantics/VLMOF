# Paper-to-artifact map

The manuscript is `paper/build/main.pdf`, built from
[`paper/main.tex`](../paper/main.tex) and [`paper/sections/`](../paper/sections/)
with `make -C paper`; the build directory is not tracked. This page connects its definitions, theorems, research
questions and Tables 1–2 to the files that support them. The claims are unchanged.
The map only says what kind of support each claim has and where to check it.

Lean checks the Lean names on this page. Run
`lake env lean experiments/PaperMap.lean` after `lake build`. It fails if a name
disappears, and it prints the axioms behind Theorems 1 and 2. The
[reproduction guide](../REPRODUCING.md) gives the commands. The
[evaluation guide](../experiments/README.md) describes the inputs and the protocol.

## Kinds of support

| Kind | Meaning | Does not establish |
|---|---|---|
| **Proved** | A Lean theorem about our definitions, checked by `lake build`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. | That the definitions match EMOF; correctness of parsing, JSON, the Java bridge, the compiler or the runtime |
| **Argued** | The correspondence between the definitions and the MOF/UML text, in Section 3.2, [`sources/CLAUSE-AUDIT.md`](../sources/CLAUSE-AUDIT.md) (all 32 restrictions of MOF §12.4) and [`sources/PROFILE.md`](../sources/PROFILE.md) | A machine-checked link to the standard |
| **Tested** | Executable interfaces outside the proofs, run on selected inputs: parser, JSON decoder, CLI, Java/EMF bridge and runners | Behaviour on inputs not tested |
| **Observed** | Outcomes of one run on named inputs: EMF decisions, loaded-state comparisons, times | Generality beyond those inputs, tools and versions |

## Section 3: definitions and theorems

| Paper | Lean declaration | File | Kind |
|---|---|---|---|
| Def. 1 Schema | `VLMOF.Schema` and its declaration records | [`VLMOF/Model/Basic.lean`](../VLMOF/Model/Basic.lean) | definition |
| Def. 2 Snapshot, values, rows | `Snapshot`, `ObjectDecl`, `Observation`, `Value` | `VLMOF/Model/Basic.lean` | definition |
| Def. 3 Lookup `L_M(o,p)` | `Snapshot.occurrences` | [`VLMOF/Model/Semantics.lean`](../VLMOF/Model/Semantics.lean) | definition |
| Applicability `app(c)`, ancestors | `Schema.applicableProperty`, `Schema.ancestors` | `VLMOF/Model/Semantics.lean` | definition |
| Def. 4 `W(S)` | `SchemaWellFormed` (fields below) | `VLMOF/Model/Semantics.lean` | definition, argued |
| Def. 5 `C(S,M)` | `SnapshotConforms`; field `schema` is `W(S)` | `VLMOF/Model/Semantics.lean` | definition, argued |
| Checker `check(S,M)` | `checkSnapshot`, `checkSchema`; named diagnostics | [`VLMOF/Checker/Basic.lean`](../VLMOF/Checker/Basic.lean) | definition |
| **Thm. 1**, Eq. (1) | `checkSnapshot_iff` | [`VLMOF/Checker/Correctness/Acceptance.lean`](../VLMOF/Checker/Correctness/Acceptance.lean) | proved |
| Proof sketch: breadth-first search finds exactly the chains | `Schema.isSubtype_iff_superReachable`, `packageClosure_iff`, `containmentClosure_iff`, `SnapshotConforms.compositeReachable_iff_path` | [`VLMOF/Model/Reachability/`](../VLMOF/Model/Reachability/) | proved |
| Def. 6 Source document | `Source.Document`, `Source.Model`, `Source.Instance` | [`VLMOF/Source/Syntax.lean`](../VLMOF/Source/Syntax.lean) | definition |
| N1–N4 (well named) | checked during binding by `Source.elaborate` | [`VLMOF/Source/Binding/`](../VLMOF/Source/Binding/) | definition |
| Lexical admissibility | `Source.LexicallyAdmissible`, `Source.NameValid` | [`VLMOF/Source/Adequacy.lean`](../VLMOF/Source/Adequacy.lean), [`Source/Semantics.lean`](../VLMOF/Source/Semantics.lean) | definition |
| Def. 7 Elaboration `E` | `Source.elaborate` | [`VLMOF/Source/Elaboration.lean`](../VLMOF/Source/Elaboration.lean) | definition |
| Def. 8 Meaning `𝒮(d)` | `Source.SourceSatisfies`, `Source.ModelWellFormed` | `VLMOF/Source/Semantics.lean` | definition |
| **Thm. 2 (i)** | `Source.elaborate_complete` | [`VLMOF/Source/Completeness.lean`](../VLMOF/Source/Completeness.lean) | proved |
| **Thm. 2 (ii)** | `Source.sourceSatisfies_iff_conforms` | `VLMOF/Source/Adequacy.lean` | proved |
| Eq. (2) | `Source.sourceSatisfies_iff_accepted`, `Source.sourceSatisfies_iff_exists_accepted` | `VLMOF/Source/Adequacy.lean` | proved |
| Running snapshot `M_T` (Figs. 2–3) and every counterexample in Section 3.2 | `mt.dsl` and one-change variants | [`examples/running-example/`](../examples/running-example/) | tested |

The library's reading order is in [`docs/README.md`](README.md). Some concrete
witnesses in `VLMOF/Examples/` use `native_decide`, which also trusts the
compiler. Theorems 1 and 2 do not use it, and `PaperMap.lean` prints their axioms.

### Conditions, Lean fields and checker diagnostics

The CLI reports a rejection by diagnostic field name. This table reads those names
back to the paper's conditions.

| Paper | `SchemaWellFormed` / `SnapshotConforms` fields | CLI diagnostic `field` |
|---|---|---|
| W1 Identities | `unique{Package,Class,Property,Association,Enumeration,Literal}Ids` | `unique … identifiers` |
| W2 Names | `names` | `declaration names` |
| W3 Resolution | `packageParentsResolved`, `classPackagesResolved`, `enumPackagesResolved`, `associationPackagesResolved`, `supersResolved`, `propertyOwnersResolved`, `propertyTypesResolved`, `literalsResolved` | `… resolved` |
| W4 Acyclicity | `packageAcyclic`, `inheritanceAcyclic` | `package hierarchy acyclic`, `inheritance acyclic` |
| W5 Properties | `multiplicities`, `compositeReferences`, `inheritedIdCount` | `multiplicities valid`, `composites reference classes`, `at most one inherited ID` |
| W6 Associations | `associationEnds`, `endMembershipUnique`, `containerUpperOne` | `association ends valid`, `unique end membership`, `container upper bound` |
| C1 Objects | `uniqueObjectIds`, `classifiersResolved`, `concreteClassifiers` | `unique object identifiers`, `classifiers resolved`, `classifiers concrete` |
| C2 Rows | `uniqueObservationKeys`, `observationsExact`, `observationKeysResolved`, `observationApplicable` | `unique observation keys`, `observations exact`, `observation keys resolved`, `observations applicable` |
| C3 Typing | `valuesTyped` | `values typed` |
| C4 Multiplicity | `bounds`, `uniqueness` | `multiplicity bounds`, `unique occurrences` |
| C5 Opposites | `oppositeCounts` | `opposite counts` |
| C6 Containment | `oneIncomingComposite` (`SingleContainer`, `SingleContainerProperty`), `containmentAcyclic` | `one container and active container property`, `containment acyclic` |
| `W(S)` inside `C(S,M)` | `schema` | `schema well formed` |

## Section 4: tool support

| Paper | Files | Kind |
|---|---|---|
| Fig. 3 grammar and textual notation | [`docs/source-language.md`](source-language.md), [`VLMOF/Source/Parser.lean`](../VLMOF/Source/Parser.lean), `Main.lean` (`check-dsl`, `check-json`) | tested |
| Core JSON decoding | [`VLMOF/Interchange/Json.lean`](../VLMOF/Interchange/Json.lean) | tested |
| "Parsing and decoding … are tested, not proved" | [`scripts/test_cli.py`](../scripts/test_cli.py), `VLMOF/Examples/Parser.lean`, [`experiments/run.py`](../experiments/run.py) | tested |
| Fig. 4 import route (Ecore + XMI to Core) | [`bridge/`](../bridge/README.md): `EmfInterchange.java` | tested |
| Fig. 4 EMF decisions and collected observations | `bridge/…/EmfValidationHarness.java` | tested |
| Fig. 4 "compare model values" | `compare_loaded_to_core` in [`experiments/run_emf_validation.py`](../experiments/run_emf_validation.py) | tested |
| Round trips (export, reimport, recheck) | [`experiments/run_public.py`](../experiments/run_public.py), `bridge/scripts/e1_export_regression.py` | tested, observed |

## Research questions: claim-to-evidence

| Claim (paper location) | Kind | Evidence | Check |
|---|---|---|---|
| **RQ1** Selected structural requirements are the predicates `W` and C1–C6 (Defs. 4–5) | definition, argued | `VLMOF/Model/Semantics.lean`; `sources/CLAUSE-AUDIT.md`; `sources/PROFILE.md` | read; `PaperMap.lean` |
| RQ1 Each Section 3.2 counterexample violates the named condition alone; the controls are accepted | tested | `examples/running-example/` | `python3 -m unittest scripts.test_cli.RunningExampleTests` |
| RQ1 Restrictions: complete snapshots, stricter mixed-uniqueness opposites, `0..0` admitted, and the exclusions in Section 6 | argued; witnesses tested | `c5-mixed-follows-twice.dsl`, `zero-zero-active.dsl`; `sources/PROFILE.md`; importer rejections in `bridge/README.md` | as above |
| **RQ2** Thm. 1: `check(S,M)=true ⇔ C(S,M)` | proved | `checkSnapshot_iff` | `lake build`; `PaperMap.lean` |
| RQ2 Thm. 2 and Eq. (2) | proved | `elaborate_complete`, `sourceSatisfies_iff_conforms`, `sourceSatisfies_iff_accepted` | `lake build`; `PaperMap.lean` |
| RQ2 Parsing, decoding and lexical admissibility of parsed names | tested | CLI tests and parser examples | `make check` |
| Sec. 5.1 Train batch-1: 10 classes, 21 features, 2 enumerations, 754 objects, 3,378 rows; accepted | observed (import tested; decision proved correct for the imported pair, assuming compiler and runtime) | historical `public-raw-alignment-01`; fresh `public/train-emf-comparison` | `reproduce.py --phase public` |
| Sec. 5.1 The generated DSL elaborates exactly to that Core pair; a one-sensor Route fails only multiplicity | tested | [`experiments/TrainWalkthrough.lean`](../experiments/TrainWalkthrough.lean), [`examples/train/full-v1-batch-1.dsl`](../examples/train/full-v1-batch-1.dsl), [`docs/train-walkthrough.md`](train-walkthrough.md) | public phase |
| Sec. 5.1 EMF Compare 3.3.28 is rejected for operations before Core checking | observed | `run_public.py` case `emf-compare-operations` | public phase |
| **RQ3** Table 1 decisions and loaded-state correspondence | observed | [below](#table-1-tracing-each-row) | `evidence.py table1` |
| RQ3 Table 2 times; 40 of 45 paired trials complete | observed | [below](#table-2-tracing-each-row) | `evidence.py table2` |
| RQ3 "Raw-list graph expansion and per-object containment reachability may explain this depth sensitivity" | hypothesis, not tested | none; no profiling or complexity bound | not applicable |
| Conclusion: "synthetic workloads identify deep containment as a practical limit" | observation on three synthetic families | Table 2 chain rows | `evidence.py table2` |

## Table 1: tracing each row

The fixture manifests (`*.fixture.json`), Ecore and XMI files are in
[`experiments/cases/emf-validation/`](../experiments/cases/emf-validation/). The
two Train rows use public inputs; see the
[evaluation guide](../experiments/README.md#train-benchmark-inputs-and-adaptations).

| Table 1 row | Fixture id(s) | Historical evidence (companion) | Fresh run (`reproduce.py`) |
|---|---|---|---|
| Aligned positives (11) | `tiny-valid`, `train-route-switch`, `containment-inheritance-{11,101,501}`, `train-projection-{10,100,500}`, `recursive-containment-{11,101,501}` | `multifamily-evaluation-03/correctness/results.json` | `correctness/emf-comparison/results.json` |
| Missing required String | `tiny-missing-required` | same | same |
| Repeated unique String | `unique-duplicate-source` | same | same |
| Train with explicit defaults | `train-batch-1-profile` | same (inputs: `third-review-public`) | `public/train-emf-comparison/results.json` |
| Train with original omissions | `public-train-raw-batch-1-profile` | `public-raw-alignment-01/results.json` | `public/train-emf-comparison/results.json` |
| Lower 1 / upper 0 | `invalid-bounds` | `multifamily-evaluation-03/correctness/results.json` | `correctness/emf-comparison/results.json` |
| Empty 0..0 | `zero-upper` | same | same |
| Repeated containment | `unpaired-repeated-containment` | same | same |
| Two unpaired features | `unpaired-two-feature-containment` | same | same |

The columns come from each fixture entry of `results.json`:

- **EMF schema** is `phases.emf_validation.report.schema_accepted`: the `Diagnostician` call on the Ecore root, using `EcoreValidator`.
- **EMF instance** is `…report.instance_accepted`: the calls on the XMI roots, using `EObjectValidator`.
- **VL-MOF** is `phases.vlmof_validation.status`: one call to `check-json` on the imported Core pair, which includes `W(S)`.
- **Panel (b)** is `phases.normalization.loaded_to_core`: `lossless`, `mismatches` and `problems`.

`python3 experiments/evidence.py table1 RESULTS.json …` prints these per fixture
and compares them with the table parsed from `paper/sections/evaluation.tex`.

## Table 2: tracing each row

| Table 2 row | Fixture | Generator parameters |
|---|---|---|
| Containment star 11/101/501 | `containment-inheritance-{11,101,501}` | `tiny.ecore`; 10/100/500 children |
| Train projection 10/100/500 | `train-projection-{10,100,500}` | `train-route-switch.ecore`; 2/20/100 groups of five objects |
| Containment chain 11/101/501 | `recursive-containment-{11,101,501}` | `recursive-containment.ecore`; depth 10/100/500 |

All nine are generated by
[`experiments/generate_scaling_cases.py`](../experiments/generate_scaling_cases.py).
Their parameters are recorded in each manifest's `generator` field. In a timing
run directory, trial *k* of fixture *f* is `timing/trial-k/f/results.json`. Its
`fixtures[0]` holds four things:

- **Objects and Rows**: `phases.normalization.loaded_to_core.core_object_count` and `core_observation_count`.
- **EMF samples**: `timing.emf.report.samples`.
- **VL-MOF samples**: `timing.lean.report.schemaAndSnapshot`, with the separate schema-only samples in `…schema`.
- **Worker record**: `timing.lean.record` and `timing.emf.record`, holding the exit status and any timeout error.

Each printed value is the median over trials of the per-process median of the 30
samples with `warmup: false`. `python3 experiments/evidence.py table2 RUN_DIR`
recomputes the table. With `--exact`, it also requires the printed times, which
only the retained historical run can meet.

## Reading the results

- **Agreeing decisions are not agreeing loaded values.** Panel (a) compares validator decisions; panel (b) compares what was loaded. The Train copy with explicit defaults is accepted by every validator, yet 12 scalar values differ in presence: EMF's `eIsSet` treats an explicit first enumeration literal as unset. The repeated unique String loads identically in both tools, yet the decisions differ.
- **Schema rejection is not instance rejection.** EMF validates the Ecore schema and the XMI instance in separate calls. VL-MOF's single check includes `W(S)`, so an instance can never be accepted under a schema it rejects. In the lower block of Table 1(a), Ecore rejects the schema and its instance validator still accepts the instance. VL-MOF accepts the `0..0` and unpaired-containment schemas; it rejects lower 1 / upper 0 as `W5`. The two-feature schema also declares a nonunique composite, so its rejection does not isolate the instance behaviour (Section 5.2).
- **Historical results are not fresh results.** The printed tables come from the retained companion evidence recorded on 15 Sep 2026 (see [`experiments/companion-evidence.json`](../experiments/companion-evidence.json)). A fresh run should reproduce every decision, state comparison, object and row count. Its times are new observations. Report them separately; they do not replace the paper's values.
- **A batch timeout is not a validation time.** "timeout" means that all five VL-MOF worker processes for the 501-deep chain exceeded the 120-second limit. That limit covers the file read, JSON decoding, 10 + 30 schema-only and 10 + 30 combined iterations, and process overhead. No sample survives such a process, so it says nothing about any single validation.
- **Observations are not bottleneck explanations.** Table 2 shows VL-MOF's sensitivity to containment depth on these workloads. The causes named in Section 5.3 are hypotheses: no profiler run and no complexity bound support them.
- **No general equivalence or speed ranking.** The EMF validators and VL-MOF check different properties: generic EObject constraints versus `C(S,M)` including `W(S)` and containment acyclicity. They ran on 17 authored or generated fixtures plus two Train variants. Agreement there does not make VL-MOF equivalent to EMF. The times do not rank the tools beyond these nine synthetic workloads, this machine and these versions.

## What is not in this checkout

- **Retained historical evidence** behind the printed numbers: logs, raw samples and loaded observations, about 146 MB. It is described, with digests, in [`experiments/companion-evidence.json`](../experiments/companion-evidence.json) and must be obtained from the authors or the companion archive.
- **Public inputs**: fetched at pinned revisions by [`experiments/cases/fetch-public-cases.sh`](../experiments/cases/fetch-public-cases.sh).
- **OMG specification files**: fetched and verified by `make sources`.

The paper states what the retained provenance cannot support (Section 6). The
generation sources were not hashed, the working tree was dirty and the hardware
record is partial. The evidence therefore permits recomputing the printed summaries
from the raw samples, not rebuilding the exact measured binaries.
