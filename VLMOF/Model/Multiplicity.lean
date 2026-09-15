/-!
# Normalized multiplicity intervals

This module isolates the arithmetic meaning of a property multiplicity from the
rest of the raw schema representation. `Upper.allows` and
`Multiplicity.intervalConsistent` describe ordinary natural-number intervals.
`multiplicityValid` adds this project's selected-profile rule that a finite upper
bound must be positive. Keeping those predicates separate makes clear that the
profile rejects `0..0` even though it is a mathematically consistent interval.

`isOrdered` and `isUnique` describe collection observation and validity; they do
not change which cardinalities the lower and upper bounds admit.

The separation and the lower-bound witness used below adapt the semantic style of
the archived multiplicity prototype at commit `16182c7`. The names and record
shape here retain the established VL-MOF API and its stricter finite-upper policy.
Source relationship: MOF 2.5.1, clauses 12.4[32] and 12.5; see
`sources/PROFILE.md` for the selected subset and exact locators.
-/

namespace VLMOF

/-- A normalized upper cardinality bound. `unlimited` is a separate constructor,
so no finite natural number is used as a sentinel for `*`. -/
inductive Upper where
  | finite (value : Nat)
  | unlimited
  deriving DecidableEq, Repr

/-- Whether `count` is no greater than this upper bound. Every natural number is
allowed by `unlimited`; this predicate contains no lower-bound or profile check. -/
@[simp] def Upper.allows (upper : Upper) (count : Nat) : Prop :=
  match upper with
  | .finite value => count ≤ value
  | .unlimited => True

/-- The normalized multiplicity metadata stored on a property. `lower` and `upper`
form the cardinality interval. The Boolean fields govern order-sensitive comparison
and duplicate validity, rather than interval arithmetic. -/
structure Multiplicity where
  lower : Nat
  upper : Upper
  isOrdered : Bool
  isUnique : Bool
  deriving DecidableEq, Repr

/-- A cardinality is admitted by the mathematical interval when it is at least the
lower bound and is allowed by the upper bound. Collection flags are deliberately
absent from this predicate. -/
def withinMultiplicity (m : Multiplicity) (n : Nat) : Prop :=
  m.lower ≤ n ∧ m.upper.allows n

/-- Namespace-oriented spelling of `withinMultiplicity` for mathematical results
about a multiplicity interval independent of snapshot conformance. -/
abbrev Multiplicity.Admits (m : Multiplicity) (n : Nat) : Prop :=
  withinMultiplicity m n

/-- The raw lower and upper bounds describe a nonempty natural-number interval.
This accepts `0..0`; selected-profile admissibility is expressed separately by
`multiplicityValid`. -/
def Multiplicity.intervalConsistent (m : Multiplicity) : Prop :=
  m.upper.allows m.lower

/-- The selected structural profile's schema-level multiplicity restriction. A
finite upper bound must be positive as well as no smaller than the lower bound;
an unlimited upper bound is always accepted. -/
def multiplicityValid (m : Multiplicity) : Prop :=
  match m.upper with
  | .finite u => 0 < u ∧ m.lower ≤ u
  | .unlimited => True

/-- Some natural cardinality is admitted exactly when the raw interval is
consistent. For the reverse direction the lower bound itself is the witness; for
the forward direction transitivity handles a finite upper bound. -/
theorem Multiplicity.exists_admitted_iff_intervalConsistent (m : Multiplicity) :
    (∃ n, m.Admits n) ↔ m.intervalConsistent := by
  cases m with
  | mk lower upper ordered unique =>
      cases upper with
      | finite upper =>
          constructor
          · rintro ⟨n, lower_le_n, n_le_upper⟩
            exact Nat.le_trans lower_le_n n_le_upper
          · intro lower_le_upper
            exact ⟨lower, Nat.le_refl lower, lower_le_upper⟩
      | unlimited =>
          constructor
          · intro _
            trivial
          · intro _
            exact ⟨lower, Nat.le_refl lower, True.intro⟩

/-- Profile-valid multiplicities always have consistent bounds. The converse does
not hold for the consistent interval `0..0`, because this profile requires positive
finite upper bounds. -/
theorem multiplicityValid_implies_intervalConsistent {m : Multiplicity}
    (h : multiplicityValid m) : m.intervalConsistent := by
  cases m with
  | mk lower upper ordered unique =>
      cases upper with
      | finite upper => exact h.2
      | unlimited => trivial

/-- Changing ordering or uniqueness metadata leaves admitted cardinalities
unchanged. This result records the boundary between interval arithmetic and
collection semantics directly in the public API. -/
theorem withinMultiplicity_withFlags (m : Multiplicity) (n : Nat)
    (ordered unique : Bool) :
    withinMultiplicity { m with isOrdered := ordered, isUnique := unique } n ↔
      withinMultiplicity m n := by
  rfl

end VLMOF
