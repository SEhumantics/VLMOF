/-!
# Normalized multiplicity intervals

This module isolates the arithmetic meaning of a property multiplicity from the
rest of the raw schema representation. `Upper.allows` and
`Multiplicity.intervalConsistent` describe ordinary natural-number intervals.
`multiplicityValid` checks interval consistency, including `0..0` as allowed
by UML 2.5, 7.5.3.2. `Multiplicity.creationBounds` separately records the
positive-upper premise of MOF 2.5.1, 9.3.3[4-5]. A prerequisite of reflective
creation must not reject an otherwise well-formed uninstantiated declaration.

`isOrdered` and `isUnique` describe collection observation and validity; they do
not change which cardinalities the lower and upper bounds admit.

Source relationship: UML 2.5, 7.5.3.2 and 7.8.8.8 define the structural
interval; MOF 2.5.1, 12.4[32] fixes literal kinds and 9.3.3[4-5] supplies
class-creation prerequisites. See `sources/PROFILE.md` for scope.
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
This accepts `0..0`; reflective creation has an additional positive-upper premise. -/
def Multiplicity.intervalConsistent (m : Multiplicity) : Prop :=
  m.upper.allows m.lower

/-- Structural multiplicity validity follows the adopted UML interval rules.
Zero upper bounds are legal when the lower bound is also zero. -/
def multiplicityValid (m : Multiplicity) : Prop :=
  match m.upper with
  | .finite u => m.lower ≤ u
  | .unlimited => True

/-- The multiplicity prerequisites of MOF Factory.create, not complete creation
semantics. The class-scoped predicate selects inherited class-owned properties. -/
def Multiplicity.creationBounds (m : Multiplicity) : Prop :=
  multiplicityValid m ∧ m.upper.allows 1

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

/-- Structural validity implies a nonempty cardinality interval. This result
concerns arithmetic feasibility, not existence of a conforming object graph. -/
theorem multiplicityValid_implies_intervalConsistent {m : Multiplicity}
    (h : multiplicityValid m) : m.intervalConsistent := by
  cases m with
  | mk lower upper ordered unique =>
      cases upper with
      | finite upper => exact h
      | unlimited => trivial

/-- The zero interval admits exactly the empty collection, while failing the
positive-upper creation premise. These are compatible contextual statements. -/
theorem zero_interval_separates_creation (ordered unique : Bool) :
    let m : Multiplicity := ⟨0, .finite 0, ordered, unique⟩
    multiplicityValid m ∧ (∀ n, m.Admits n ↔ n = 0) ∧ ¬ m.creationBounds := by
  simp [multiplicityValid, Multiplicity.Admits, withinMultiplicity,
    Multiplicity.creationBounds, Upper.allows]

/-- Changing ordering or uniqueness metadata leaves admitted cardinalities
unchanged. This result records the boundary between interval arithmetic and
collection semantics directly in the public API. -/
theorem withinMultiplicity_withFlags (m : Multiplicity) (n : Nat)
    (ordered unique : Bool) :
    withinMultiplicity { m with isOrdered := ordered, isUnique := unique } n ↔
      withinMultiplicity m n := by
  rfl

end VLMOF
