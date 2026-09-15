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

The selected schema profile adds a different condition: a finite upper bound must
be positive. Thus `0..0` is a consistent mathematical interval admitting zero,
but fails `multiplicityValid`. The restriction is tied to MOF 2.5.1's class-creation
prerequisites in 9.3.3[4–5], printed page 13. It is not a statement that UML cannot
represent `0..0`. [The profile](../sources/PROFILE.md) records this interpretation.

Changing ordering or uniqueness does not change admitted cardinalities, as
`withinMultiplicity_withFlags` proves. It can still change whether an actual
collection conforms. For example, a three-element list over Boolean values can
meet the interval `3..3` but cannot be duplicate-free: there are only two Boolean
values. Interval feasibility is therefore not a theorem that a conforming object
model exists. Typing, uniqueness, opposites and containment add their own obligations
in [Model.Semantics](../VLMOF/Model/Semantics.lean).

The design and lower-bound witness adapt the earlier `Multiplicity.lean`
development in the archived `VL-MOF-20260914` repository (commit `16182c7`). That
prototype separated `Allows`, `Admits` and well-formed bounds. The current module
keeps that conceptual separation while preserving the existing record API and
making the stronger profile condition explicit. The old archive remains unchanged.
