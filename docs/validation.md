# Actual EMF structural-validation experiment

This experiment compares declared finite states with actual EMF validation and
the VL-MOF checker. Outcome and diagnostic alignment come before timing. It does
not evaluate Train Benchmark queries or repair, OCL, EMF Compare, an Eclipse
editor, or relative checker speed.

## Pinned EMF condition

The bridge POM pins `org.eclipse.emf.ecore` and
`org.eclipse.emf.ecore.xmi` to 2.39.0 under Java 21. The experiment records the
resolved Maven dependency tree and hashes. Its actual entry point is
`org.vlmof.bridge.EmfValidationHarness`, not `EmfInterchange`:

```sh
mvn -q -f bridge/pom.xml exec:java \
  -Dexec.mainClass=org.vlmof.bridge.EmfValidationHarness \
  "-Dexec.args=validate experiments/cases/emf-validation/tiny-valid.fixture.json"
```

The harness creates a fresh manifest-closed resource set and isolated
`EValidatorRegistryImpl`. It selects `EcoreValidator` for Ecore schema objects
and records `EObjectValidator` fallback selection for dynamic Ecore packages.
It validates every manifest-ordered Ecore and instance root through a
fresh-context `Diagnostician`, retaining flattened diagnostics and registry
inventory. The harness configures no validation delegates; its report also
enumerates any `validationDelegates` annotations declared by the loaded
metamodel, without claiming to inventory EMF process-wide delegate registries.
It does not use global `Diagnostician.INSTANCE`, save resources, or call E1
profile checks as validation.

## State alignment

Fixtures name immutable Ecore/XMI bytes. The harness validates the `emf-loaded`
state. The runner separately uses the E1 bridge to write normalized Core JSON,
then compares native object/classifier inventories and every loaded
object/property list through native URI identity maps. Declaration inventories
check class, property, enumeration and literal coverage, with property owners,
ordering, types and literal owners checked against the mapped records. Objects
without features remain visible through the separate object inventory.
The comparison rejects duplicate or missing rows and non-bijective provenance
maps; it does not treat an absent row as an empty feature list. “Lossless” means
equality of these selected mapped identities and observations, not a general
EMOF/Ecore metamodel-equivalence theorem. The contract forbids deduplicating
nonunique values, merging rows, completing opposites, repairing containment,
resolving undeclared resources, or replacing integers.

The aligned condition excludes declared defaults and `unsettable` features.
Original XML lexical presence distinguishes omission from explicit `false`, `0`,
or empty string. Defaults/unset histories, unsupported Ecore features, and
states that need a change to represent are boundaries, not matched rejections.

The local corpus includes aligned positives/negatives and explicit separators.
VL-MOF structurally accepts `0..0`, whereas Ecore 2.39.0 rejects an upper bound
of zero; Factory creation has a separate positive-upper premise. Ecore's
`ConsistentUnique` diagnostic code 50 rejects the unpaired nonunique containment
schema separators, so those are schema-domain observations rather than evidence
about EMF instance-container behavior. The unique lexical duplicate fixture
retains two loaded values while generic EObjectValidator accepts it; it is an
unscored validator/predicate difference, not presumed normalization loss.

## Reproduction and evidence

Run correctness-only observations into a new directory:

```sh
python3 experiments/run_emf_validation.py --output /absolute/new-results
```

By default the runner selects every fixture whose inputs lie inside the
repository. It records any other manifest as not selected; pass such a manifest
explicitly with `--fixture`. Missing inputs stop the run before anything is written.
The [reproduction guide](../REPRODUCING.md) runs this and the steps below through
one wrapper.

The runner hashes sources before and after, records commands, stdout/stderr,
environment, normalized files, EMF reports, Lean reports, and unexpected
results. It never overwrites or resumes. VL-MOF exit 1 is a semantic rejection,
separate from malformed input and execution failure.

Build the separate measurement executable and Java harness before timing:

```sh
lake build validationBench
mvn -q -f bridge/pom.xml test-compile
```

After a quiescent pinned build, `--measure` enables the positive-only timing
condition with 10 warmups and 30 retained repetitions:

```sh
python3 experiments/run_emf_validation.py --measure --output /absolute/new-results
```

The paired boundary is preloaded combined schema plus instance/snapshot
validation. EMF validates all roots with fresh contexts and no diagnostics/JSON
allocation inside the clock. Lean decodes once and retains noinline IO-reference
schema and combined-check results per iteration; combined checking includes
schema validity. Full diagnostics remain outside timing. Load, normalization,
decode and cold process costs are retained separately and are never speed ratios.
The runner starts those timed commands only when the fixture declares itself
timing-eligible, both validators accept it, and its retained loaded-to-Core
comparison is explicitly lossless.

The multifamily runner regenerates the deterministic star, recursive-chain and
Train projection workloads into its output directory, requires them to equal the
committed fixtures byte for byte, runs correctness first, then launches independent trials
with both tool orders for each fixed case. Reversing case traversal does not
change the case's stable scheduling index. Worker failures, missing reports and
incomplete or rejected sample arrays must fail the timing condition rather than
being hidden by successful untimed validation.

```sh
python3 experiments/run_fifth_evaluation.py --output /absolute/new-multifamily-results
```

The run records warmups, repetitions and independent process trials separately.
Invalid or unsupported cases are correctness evidence, not timed positives.
