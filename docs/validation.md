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
inventory. It does not use global `Diagnostician.INSTANCE`, save resources, or
call E1 profile checks as validation.

## State alignment

Fixtures name immutable Ecore/XMI bytes. The harness validates the `emf-loaded`
state. The runner separately uses the E1 bridge to write normalized Core JSON,
then runs VL-MOF on that file. Normalization preserves identity allocation and
ordered occurrences; it does not deduplicate nonunique values, merge rows,
complete opposites, repair containment, resolve undeclared resources, or replace
integers.

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

The runner hashes sources before and after, records commands, stdout/stderr,
environment, normalized files, EMF reports, Lean reports, and unexpected
results. It never overwrites or resumes. VL-MOF exit 1 is a semantic rejection,
separate from malformed input and execution failure.

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
