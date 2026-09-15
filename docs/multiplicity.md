# Multiplicity: an interval before a model constraint

[Model.Multiplicity](../VLMOF/Model/Multiplicity.lean) starts with a natural lower
bound and either a finite natural upper bound or `unlimited`. Unlimited is a
constructor, not a large numeric sentinel. The ordering and uniqueness flags are
retained in the property metadata, but do not participate in interval arithmetic.

`m.Admits n` means that the cardinality `n` is at least the lower bound and no
greater than a finite upper bound. `m.intervalConsistent` means that the lower
bound itself is allowed by the upper bound. The central elementary result is:

```lean
(∃ n, m.Admits n) ↔ m.intervalConsistent
```

For a finite upper bound, any admitted `n` gives lower ≤ n ≤ upper, so transitivity
establishes consistency. Conversely, the lower bound is an admitted witness.
For an unlimited upper bound that same witness works without an upper inequality.
This argument is independent of a particular metamodel or checker implementation.

Structural validity accepts `0..0`: it admits exactly an empty occurrence list.
This follows UML 2.5, 7.5.3.2 and 7.8.8.8. MOF 2.5.1, 9.3.3[4-5] separately
requires positive upper bounds before `Factory.create` instantiates a class.
`Multiplicity.creationBounds` expresses the bound prerequisite;
`Schema.classCreationBounds` applies it to a resolved class and its inherited
class-owned properties. It does not implement creation or establish its other
preconditions. Association-owned incidence ends are not reflective class properties.

`zeroBound_empty_conforms` and `zeroBound_nonempty_rejected` in
[the conformance examples](../VLMOF/Examples/Conformance.lean) exhibit both sides:
a valid zero-bound schema has an empty conforming snapshot, while a nonempty
reference is rejected. `zeroBound_not_creation_ready` separates static conformance
from the bound prerequisite of reflective creation. The distinction matters for
schemas inspected before use, abstract classes and future operation semantics.

Changing ordering or uniqueness does not change admitted cardinalities, as
`withinMultiplicity_withFlags` proves. It can still change whether an actual
collection conforms. For example, a three-element list over Boolean values can
meet the interval `3..3` but cannot be duplicate-free: there are only two Boolean
values. Interval feasibility is therefore not a theorem that a conforming object
model exists. Typing, uniqueness, opposites and containment add their own obligations
in [Model.Semantics](../VLMOF/Model/Semantics.lean).

The lower-bound witness preserves the earlier development's distinction between
interval feasibility and graph existence. No reflection or reachability theorem
is implied by structural checker acceptance.
