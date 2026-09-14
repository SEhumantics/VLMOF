# Reproducible public EMF evaluation

`run_public.py` records the bounded public evaluation as a new, immutable evidence
directory. It requires local checkouts at these exact public revisions:

- Train Benchmark: `6490047d7449f9a4b66cec032b9377bfc06a54d2`
- EMF Compare: `9f25a964c1be423373587d8063a5b132714ebeae`

Build the checker represented by the current VL-MOF checkout, or point `CHECKER`
at an already built executable whose repository provenance should be recorded. Then
run:

```sh
CHECKER=/absolute/VL-MOF/.lake/build/bin/vlmof \
python3 experiments/run_public.py \
  --train /absolute/public-cases/trainbenchmark \
  --emf-compare /absolute/public-cases/emf-compare \
  --output /absolute/reports/evaluation/public-runner-01
```

The output path must not exist. The runner neither deletes it nor resumes a partial
run. It rejects a checkout with a different revision or a change to any evaluated
Xcore, XMI, or Ecore file. Unrelated checkout changes do not affect the pin check,
but the runner records the overall dirty state. It hashes the public inputs again at
the end to establish that the raw files stayed unchanged during execution.

For each of the six Train snapshots, the runner compiles the pinned Xcore metamodel,
applies the explicit profile metamodel adaptation, and writes a separate XMI copy
whose inserted enum defaults are listed in a per-snapshot JSON manifest. It then
imports that copy through EMF, checks the E1 document with the Lean/Core executable,
exports fresh dynamic Ecore and XMI resources, reimports them, compares the two E1
documents using the exporter's explicit native-identity sidecar, and checks the
reimported document again. The raw Xcore and XMI files remain in their public
checkouts. These six acceptances establish the behavior of the explicitly adapted
inputs; they are not claims that the raw resources conform unchanged.

Two controls make that boundary executable. The Xcore compiler's generated Ecore is
passed to the importer before the metamodel adaptation and is expected to be
`unsupported` because it retains generator annotations. Raw Train batch 1 is also
imported with the adapted profile metamodel, without default materialization. Core
accepts it because both enum properties have lower bound zero. The control records
six empty `position` and six empty `currentPosition` observations, showing that
materialization preserves intended EMF runtime-default meaning rather than repairing
Core conformance. The pinned EMF Compare `compare.ecore` is passed to the real
importer and is expected to be `unsupported` because the declared E1 profile
excludes operations.

`results.json` is the structured index. Every invoked process has its argument list,
working directory, exit code, wall duration, and retained stdout/stderr file with
byte count and SHA-256 digest. It also records repository and checker commits and
dirty states; Java, Maven, Lean, Python, kernel, and CPU evidence; the checker,
adapter, runner, build, complete bridge Java source set, and public-input hashes;
Maven's resolved dependency tree; generated artifact hashes; and the adaptation
manifests. The five result classes are `accepted`, `rejected`,
`unsupported`, `not-run`, and `execution-failure`. A prerequisite failure makes its
dependent stages `not-run`; tool launch failures and inconsistent or unparseable
structured results are `execution-failure`. The command exits zero only when every
adapted Train route and the raw-snapshot control are accepted, both unsupported
controls match their expected diagnostics, and the raw inputs are unchanged.

All durations are one-run operational wall-clock records. They are retained to make
the run auditable, not to claim benchmark performance or superiority.
