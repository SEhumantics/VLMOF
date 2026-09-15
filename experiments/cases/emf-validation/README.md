# Actual EMF validation fixtures

These fixtures are deliberately small isolating states for the W5/W6 protocol.
They are not a substitute for the selected Train route-switch-position case or
the retained public Train inputs. Each `*.fixture.json` names a schema/XMI
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
one root. They deliberately have no expected validation result. The retained
normalization output establishes whether native EMF represented, rejected, or
reparented each source before it can be discussed against VL-MOF's corrected
containment semantics.

Fixtures excluded by the E1 default contract, and direct/static containment
separators, are added only with their loaded-state observations and reviewed
semantic mapping. Never turn one into a matched rejection by modifying it during
normalization.
