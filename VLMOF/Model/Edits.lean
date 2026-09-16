import VLMOF.Model.Properties

/-!
# A bounded structural edit

Toggling Boolean values at one slot models an update such as Train's Route.active.
This is an operation on complete raw snapshots, not a reflective EMOF service.
It changes no identities, presence, cardinalities, or references. Boolean negation
is injective, so uniqueness is also preserved. The result below composes these
facts for all fields of SnapshotConforms, including containment reachability.
Domain predicates such as Train's SwitchSet are deliberately outside this result.
-/
namespace VLMOF

/-- Negate Boolean occurrences, retaining every other value verbatim. This total
function can operate on raw data; it does not manufacture Boolean values at a
non-Boolean slot or turn an empty optional slot into a present value. -/
def flipBoolean : Value → Value
  | .boolean b => .boolean (!b)
  | v => v

private theorem flip_twice (v : Value) : flipBoolean (flipBoolean v) = v := by
  cases v <;> simp [flipBoolean]

private theorem flip_injective : Function.Injective flipBoolean := by
  intro a b h
  have := congrArg flipBoolean h
  simpa only [flip_twice] using this

private theorem flip_nodup {xs : List Value} (h : xs.Nodup) :
    (xs.map flipBoolean).Nodup := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
      exact hn (flip_injective he ▸ hw)
    · exact ih ht

private theorem flip_reference (v : Value) (r : ObjectId) :
    flipBoolean v = .reference r ↔ v = .reference r := by
  cases v <;> simp [flipBoolean]

private theorem flip_typed (s : Schema) (m : Snapshot) (t : ValueType) (v : Value) :
    valueMatches s m t (flipBoolean v) ↔ valueMatches s m t v := by
  cases t <;> cases v <;> simp only [flipBoolean, valueMatches]

/-- Preserve a row's identity and toggle each Boolean occurrence exactly when it
has the selected object/property key. Duplicate rows remain raw duplicate rows. -/
def toggleBooleanRow (o : ObjectId) (p : PropertyId) (a : Observation) : Observation :=
  { a with occurrences := if a.object = o ∧ a.property = p
      then a.occurrences.map flipBoolean else a.occurrences }

/-- Toggle one logical slot without inserting rows, values, or inverse links.
For a conforming Boolean scalar, a present singleton is negated. Optional absence
stays absent; a non-Boolean slot is unchanged. -/
def toggleBooleanSlot (m : Snapshot) (o : ObjectId) (p : PropertyId) : Snapshot :=
  { m with observations := m.observations.map (toggleBooleanRow o p) }

private theorem row_ref (o : ObjectId) (p : PropertyId) (a : Observation) (r : ObjectId) :
    .reference r ∈ (toggleBooleanRow o p a).occurrences ↔ .reference r ∈ a.occurrences := by
  simp only [toggleBooleanRow]
  split
  · simp only [List.mem_map]
    constructor
    · rintro ⟨v, hv, he⟩
      exact (flip_reference v r).mp he ▸ hv
    · intro h; exact ⟨.reference r, h, rfl⟩
  · rfl

private theorem slot_occurrences (m : Snapshot) (o x : ObjectId) (p q : PropertyId) :
    (toggleBooleanSlot m o p).occurrences x q =
      if x = o ∧ q = p then (m.occurrences x q).map flipBoolean else m.occurrences x q := by
  rcases m with ⟨objects, observations⟩
  induction observations with
  | nil => simp [toggleBooleanSlot, Snapshot.occurrences]
  | cons a rest ih =>
    simp only [toggleBooleanSlot, List.map_cons, Snapshot.occurrences,
      List.filter_cons] at *
    by_cases h : a.object = x ∧ a.property = q
    · rcases h with ⟨hx, hq⟩
      simp [toggleBooleanRow, hx, hq, List.map_append]
      split <;> simp_all
    · have h' : ¬((toggleBooleanRow o p a).object = x ∧
          (toggleBooleanRow o p a).property = q) := h
      simpa only [h, h', decide_false, Bool.false_eq_true, ↓reduceIte] using ih

private theorem flip_count (xs : List Value) (r : ObjectId) :
    (xs.map flipBoolean).count (.reference r) = xs.count (.reference r) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => simp [List.count_cons, flip_reference, ih]

private theorem flip_refs (xs : List Value) :
    (xs.map flipBoolean).filterMap (fun v => match v with | .reference x => some x | _ => none) =
    xs.filterMap (fun v => match v with | .reference x => some x | _ => none) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases v <;> simp [flipBoolean, ih]

private theorem toggle_outgoing (s : Schema) (m : Snapshot) (o : ObjectId)
    (p : PropertyId) (ids : List ObjectId) :
    outgoingComposite s (toggleBooleanSlot m o p) ids = outgoingComposite s m ids := by
  rcases m with ⟨objects, observations⟩
  induction observations with
  | nil => rfl
  | cons a rest ih =>
    simp only [outgoingComposite, toggleBooleanSlot, List.map_cons, List.filter_cons] at *
    by_cases h : ids.contains a.object
    · simp only [toggleBooleanRow, h, ↓reduceIte, List.flatMap_cons]
      rw [ih]
      split <;> simp only [List.append_cancel_right_eq]
      · split
        · exact flip_refs _
        · rfl
    · simpa only [toggleBooleanRow, h, Bool.false_eq_true, ↓reduceIte] using ih

private theorem toggle_composite (s : Schema) (o : ObjectId) (p : PropertyId)
    (a : Observation) (r : ObjectId) :
    compositeObservation s (toggleBooleanRow o p a) r = compositeObservation s a r := by
  simp only [compositeObservation, toggleBooleanRow]
  split <;> simp_all [flip_reference]

/-- Boolean-slot toggling preserves every structural conformance obligation for
any represented schema and conforming complete snapshot. No output-conformance
premise or rerun of the checker is required. Injectivity preserves uniqueness;
unchanged references preserve opposite counts and the entire containment graph.
This does not preserve arbitrary domain constraints involving Boolean values. -/
theorem toggleBooleanSlot_conforms {s : Schema} {m : Snapshot}
    (h : SnapshotConforms s m) (o : ObjectId) (p : PropertyId) :
    SnapshotConforms s (toggleBooleanSlot m o p) := by
  have reach (x y : ObjectId) :
      compositeReachable s (toggleBooleanSlot m o p) x y ↔ compositeReachable s m x y := by
    unfold compositeReachable
    simp only [toggleBooleanSlot]
    have he : outgoingComposite s (toggleBooleanSlot m o p) = outgoingComposite s m :=
      funext (toggle_outgoing s m o p)
    change y ∈ iterateClosure (outgoingComposite s (toggleBooleanSlot m o p)) m.objects.length [x] ↔ _
    rw [he]
  refine {
    schema := h.schema
    uniqueObjectIds := h.uniqueObjectIds

    uniqueObservationKeys := ?_
    classifiersResolved := h.classifiersResolved

    concreteClassifiers := h.concreteClassifiers
    observationsExact := ?_

    observationKeysResolved := ?_
    observationApplicable := ?_
    valuesTyped := ?_

    bounds := ?_
    uniqueness := ?_
    oppositeCounts := ?_
    oneIncomingComposite := ?_

    containmentAcyclic := ?_ }
  · change (List.map Observation.key (List.map (toggleBooleanRow o p) m.observations)).Nodup
    rw [List.map_map]
    exact h.uniqueObservationKeys
  · intro x hx q hq
    rw [← h.observationsExact x hx q hq]
    constructor
    · rintro ⟨a, ha, ho, hp⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ⟨b, hb, ho, hp⟩
    · rintro ⟨a, ha, ho, hp⟩
      exact ⟨toggleBooleanRow o p a, List.mem_map.mpr ⟨a, ha, rfl⟩, ho, hp⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact h.observationKeysResolved b hb
  · intro a ha x hx he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact h.observationApplicable b hb x hx he
  · intro a ha q hq he v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    simp only [toggleBooleanRow] at hv he
    split at hv
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      have ht := h.valuesTyped b hb q hq he w hw
      simpa only [valueMatches, toggleBooleanSlot] using (flip_typed s m q.type w).mpr ht
    · simpa [valueMatches, toggleBooleanSlot] using h.valuesTyped b hb q hq he v hv
  · intro x hx q hq happ
    rw [slot_occurrences]
    split <;> simpa using h.bounds x hx q hq happ
  · intro x hx q hq happ hu
    rw [slot_occurrences]
    split
    · exact flip_nodup (h.uniqueness x hx q hq happ hu)
    · exact h.uniqueness x hx q hq happ hu
  · intro a ha q r he x hx y hy
    simp only [slot_occurrences]
    split <;> split <;> simpa only [flip_count] using h.oppositeCounts a ha q r he x hx y hy
  · intro x hx
    obtain ⟨hc, hp⟩ := h.oneIncomingComposite x hx
    constructor
    · intro a ha b hb hca hcb
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      exact hc a' ha' b' hb' (by simpa only [toggle_composite] using hca)
        (by simpa only [toggle_composite] using hcb)
    · intro a ha b hb hax hbx hca hcb hna hnb
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      apply hp a' ha' b' hb' hax hbx hca hcb
      · intro he; simp [toggleBooleanRow, he] at hna
      · intro he; simp [toggleBooleanRow, he] at hnb
  · intro x hx y hedge
    obtain ⟨a, ha, hax, q, hq, he, hc, hv⟩ := hedge
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    intro hr
    exact h.containmentAcyclic x hx y ⟨a', ha', hax, q, hq, he, hc,
      (row_ref o p a' y).mp hv⟩ ((reach y x.id).mp hr)

/-- The edit is reversible even on malformed raw snapshots: applying it twice
restores every row and occurrence, without assuming conformance. -/
theorem toggleBooleanSlot_twice (m : Snapshot) (o : ObjectId) (p : PropertyId) :
    toggleBooleanSlot (toggleBooleanSlot m o p) o p = m := by
  have hr (a : Observation) : toggleBooleanRow o p (toggleBooleanRow o p a) = a := by
    cases a with
    | mk ao ap av =>
      simp only [toggleBooleanRow]
      split <;> simp_all [List.map_map, Function.comp_def, flip_twice]
  cases m with
  | mk objects observations =>
    simp only [toggleBooleanSlot, List.map_map]
    congr 1
    simp only [Function.comp_def, hr]
    exact List.map_id observations

end VLMOF
