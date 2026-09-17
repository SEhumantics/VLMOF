# Actual EMF validation fixtures

These fixtures contain small isolating states and the authored Train
route-switch-position projection. The `train-batch-1-profile.fixture.json`
manifest additionally points to full public Train inputs outside this repository;
those resources are not bundled in this directory. See the
[evaluation file index](../../README.md) for exact locations and acquisition. Each `*.fixture.json` names a schema/XMI
manifest, expected result only where its semantics have been reviewed, and a
state relation. The runner hashes the original bytes before and after execution.

`tiny-valid` is the positive timing seed: nested inheritance, a containment
tree, declared opposite, required scalar fields and an ordered nonunique EInt
list. `tiny-missing-required` removes a required `Child.name`. `invalid-bounds`
puts `lowerBound=1, upperBound=0` in the schema. `unique-duplicate-source` is
intentionally a separator: it asks the harness to retain the source bytes and
the observed loaded graph before anyone claims whether EMF's unique EList has
preserved, rejected, or normalized the duplicate lexical tokens.

`zero-upper` is also deliberately not an agreement case. VL-MOF's current
structural multiplicity accepts `0..0`, while Factory creation has a separate
positive-upper premise. The pinned Ecore validator rejects an ETypedElement
upper bound of zero. Its expected disagreement is recorded so neither outcome
is misreported as a harness defect.

The two `unpaired-*-containment` fixtures make raw XMI name the same contained
object twice: first in one nonunique feature, then in two unpaired features of
one root. EcoreValidator rejects this schema family with its `ConsistentUnique`
rule (diagnostic code 50: a containment/bidirectional reference needs uniqueness
unless its upper bound is one). That is a schema-domain difference, not evidence
that EMF's loaded instance violates a one-container rule. The fixtures have no
expected score; their retained loaded observations show any representation or
reparenting separately.

Fixtures excluded by the E1 default contract, and direct/static containment
separators, are added only with their loaded-state observations and reviewed
semantic mapping. Never turn one into a matched rejection by modifying it during
normalization.

`train-route-switch` is the dynamic Ecore/XMI realization of the selected,
authored Train projection in [`examples/train/route-switch.dsl`](../../../examples/train/route-switch.dsl)
and [`docs/train-case.md`](../../../docs/train-case.md). It is a positive
published-case structural workload eligible for paired timing. It is not an
upstream generated Train XMI and it does not include Train queries or repair.
