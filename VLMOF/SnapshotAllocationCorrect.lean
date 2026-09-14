import VLMOF.OccurrenceBindingCorrect

/-!
# Snapshot allocation guarantees

Successful instance binding allocates one core object at every source-object
position and binds every source observation without changing its position.  The
proofs below invert the actual `bindInstance` computation; none assumes target
conformance or repeats the desired allocation properties as a premise.
-/
namespace VLMOF.Source

variable {α β ε : Type}

private theorem mapM_ok_cons {f : α → Except ε β} {x : α} {xs : List α} {ys : List β}
    (h : (x :: xs).mapM f = .ok ys) :
    ∃ y rest, ys = y :: rest ∧ f x = .ok y ∧ xs.mapM f = .ok rest := by
  cases hx : f x with
  | error error => simp [List.mapM_cons, hx, Bind.bind, Except.bind] at h
  | ok y =>
      cases hxs : xs.mapM f with
      | error error => simp [List.mapM_cons, hx, hxs, Bind.bind, Except.bind] at h
      | ok rest =>
          simp [List.mapM_cons, hx, hxs, Bind.bind, Except.bind, pure, Except.pure] at h
          exact ⟨y, rest, h.symm, rfl, rfl⟩

/-- Successful `mapM` preserves positions and exposes the successful computation
which produced the element at a given source position. -/
theorem mapM_ok_getElem? {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {index : Nat} {x : α}
    (hx : xs[index]? = some x) :
    ∃ y, ys[index]? = some y ∧ f x = .ok y := by
  induction xs generalizing ys index with
  | nil => simp at hx
  | cons first rest ih =>
      obtain ⟨target, targets, rfl, hfirst, hrest⟩ := mapM_ok_cons h
      cases index with
      | zero =>
          simp at hx
          subst first
          exact ⟨target, rfl, hfirst⟩
      | succ index =>
          exact ih hrest hx

/-- The converse positional view: an output at an index exposes the input and
successful mapped computation at the same index. -/
theorem mapM_ok_getElem?_target {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {index : Nat} {y : β}
    (hy : ys[index]? = some y) :
    ∃ x, xs[index]? = some x ∧ f x = .ok y := by
  induction xs generalizing ys index with
  | nil =>
      change Except.ok [] = Except.ok ys at h
      have hys : ys = [] := Except.ok.inj h.symm
      subst ys
      simp at hy
  | cons first rest ih =>
      obtain ⟨target, targets, rfl, hfirst, hrest⟩ := mapM_ok_cons h
      cases index with
      | zero =>
          simp at hy
          subst target
          exact ⟨first, rfl, hfirst⟩
      | succ index =>
          exact ih hrest hy

/-- Every target element produced by a successful `mapM` comes from a source
element on which the mapped computation succeeded. -/
theorem mapM_ok_target_mem {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
      change Except.ok [] = Except.ok ys at h
      have hys : ys = [] := Except.ok.inj h.symm
      subst ys
      simp at hy
  | cons first rest ih =>
      obtain ⟨target, targets, rfl, hfirst, hrest⟩ := mapM_ok_cons h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨first, by simp, hfirst⟩
      · obtain ⟨source, hsource, hs⟩ := ih hrest hy
        exact ⟨source, List.mem_cons_of_mem first hsource, hs⟩

/-- The object-allocation step used for each indexed source object. -/
def bindObjectAllocation (model : Model) (entry : Object × Nat) : BindingResult ObjectDecl := do
  let classifier ← classId model entry.1.classifier
  pure { id := ⟨entry.2⟩, classifier }

/-- The observation-allocation step used for each source observation. -/
def bindObservationAllocation (model : Model) (snapshot : Instance)
    (entry : Source.Observation) : BindingResult VLMOF.Observation := do
  let object ← objectId snapshot entry.object
  let property ← propertyId model entry.property
  let occurrences ← entry.occurrences.mapM (bindValue model snapshot)
  pure { object, property, occurrences }

/-- Inversion of successful instance binding into the alias check and the two
ordered allocation computations used by `bindInstance`. -/
theorem bindInstance_ok_iff (model : Model) (snapshot : Instance) (target : Snapshot) :
    bindInstance model snapshot = .ok target ↔
      checkAliases "object" (snapshot.objects.map Object.alias) = .ok () ∧
      snapshot.objects.zipIdx.mapM (bindObjectAllocation model) = .ok target.objects ∧
      snapshot.observations.mapM (bindObservationAllocation model snapshot) =
        .ok target.observations := by
  change (do
    checkAliases "object" (snapshot.objects.map Object.alias)
    let objects ← snapshot.objects.zipIdx.mapM (bindObjectAllocation model)
    let observations ← snapshot.observations.mapM (bindObservationAllocation model snapshot)
    pure ({ objects, observations } : Snapshot)) = .ok target ↔ _
  cases hc : checkAliases "object" (snapshot.objects.map Object.alias) <;>
    cases ho : snapshot.objects.zipIdx.mapM (bindObjectAllocation model) <;>
    cases hb : snapshot.observations.mapM (bindObservationAllocation model snapshot) <;>
    cases target <;>
    simp [Bind.bind, Except.bind, pure, Except.pure]

/-- Convenient one-way form of `bindInstance_ok_iff`: successful binding exposes
both allocation `mapM` equalities directly. -/
theorem bindInstance_ok_mapM {model : Model} {snapshot : Instance} {target : Snapshot}
    (h : bindInstance model snapshot = .ok target) :
    snapshot.objects.zipIdx.mapM (bindObjectAllocation model) = .ok target.objects ∧
    snapshot.observations.mapM (bindObservationAllocation model snapshot) =
      .ok target.observations :=
  ((bindInstance_ok_iff model snapshot target).mp h).2

private theorem bindObjectAllocation_ok_iff (model : Model) (entry : Object × Nat)
    (target : ObjectDecl) :
    bindObjectAllocation model entry = .ok target ↔
      ∃ classifier, classId model entry.1.classifier = .ok classifier ∧
        target = { id := ⟨entry.2⟩, classifier } := by
  cases hc : classId model entry.1.classifier <;> cases target <;>
    simp [bindObjectAllocation, hc, Bind.bind, Except.bind, pure, Except.pure, eq_comm]

private theorem bindObservationAllocation_ok_iff (model : Model) (snapshot : Instance)
    (source : Source.Observation) (target : VLMOF.Observation) :
    bindObservationAllocation model snapshot source = .ok target ↔
      objectId snapshot source.object = .ok target.object ∧
      propertyId model source.property = .ok target.property ∧
      OccurrencesBind model snapshot source.occurrences target.occurrences := by
  rw [← bindOccurrences_iff]
  cases ho : objectId snapshot source.object <;>
    cases hp : propertyId model source.property <;>
    cases hv : source.occurrences.mapM (bindValue model snapshot) <;>
    cases target <;>
    simp [bindObservationAllocation, ho, hp, hv, Bind.bind, Except.bind, pure, Except.pure]

/-- Every bound observation is backed by an original source observation and by
the successful object, property, and occurrence binding operations that created it. -/
theorem boundObservation_source {model : Model} {snapshot : Instance} {target : Snapshot}
    (h : bindInstance model snapshot = .ok target)
    {observation : VLMOF.Observation} (hm : observation ∈ target.observations) :
    ∃ source ∈ snapshot.observations,
      objectId snapshot source.object = .ok observation.object ∧
      propertyId model source.property = .ok observation.property ∧
      OccurrencesBind model snapshot source.occurrences observation.occurrences := by
  have hmap := (bindInstance_ok_mapM h).2
  obtain ⟨source, hsource, hs⟩ := mapM_ok_target_mem hmap hm
  exact ⟨source, hsource,
    (bindObservationAllocation_ok_iff model snapshot source observation).mp hs⟩

/-- At each source-object index, successful binding creates exactly the core
object whose identifier is that index and whose classifier is the resolved alias. -/
theorem boundObject_at_index {model : Model} {snapshot : Instance} {target : Snapshot}
    (h : bindInstance model snapshot = .ok target) {index : Nat} {source : Object}
    (hs : snapshot.objects[index]? = some source) :
    ∃ classifier,
      classId model source.classifier = .ok classifier ∧
      target.objects[index]? = some ({ id := ⟨index⟩, classifier } : ObjectDecl) := by
  have hz : snapshot.objects.zipIdx[index]? = some (source, index) := by
    simp [List.getElem?_zipIdx, hs]
  obtain ⟨object, ho, hb⟩ := mapM_ok_getElem? (bindInstance_ok_mapM h).1 hz
  obtain ⟨classifier, hc, rfl⟩ :=
    (bindObjectAllocation_ok_iff model (source, index) object).mp hb
  exact ⟨classifier, hc, ho⟩

/-- The identifier stored in any allocated object is exactly its list position. -/
theorem boundObject_id_eq_index {model : Model} {snapshot : Instance} {target : Snapshot}
    (h : bindInstance model snapshot = .ok target) {index : Nat} {object : ObjectDecl}
    (ho : target.objects[index]? = some object) : object.id = ⟨index⟩ := by
  obtain ⟨entry, he, hb⟩ := mapM_ok_getElem?_target (bindInstance_ok_mapM h).1 ho
  rw [List.getElem?_zipIdx] at he
  cases hs : snapshot.objects[index]? with
  | none => simp [hs] at he
  | some source =>
      simp [hs] at he
      subst entry
      obtain ⟨classifier, hc, ht⟩ :=
        (bindObjectAllocation_ok_iff model (source, index) object).mp hb
      simp [ht]

/-- Allocated object identifiers are unique within the bound snapshot. -/
theorem boundObject_id_injective {model : Model} {snapshot : Instance} {target : Snapshot}
    (h : bindInstance model snapshot = .ok target)
    {first second : ObjectDecl} (hf : first ∈ target.objects) (hs : second ∈ target.objects)
    (hid : first.id = second.id) : first = second := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
  have hfi := boundObject_id_eq_index h hi
  have hsj := boundObject_id_eq_index h hj
  have hij : i = j := ObjectId.mk.inj (hfi.symm.trans (hid.trans hsj))
  subst j
  exact Option.some.inj (hi.symm.trans hj)

/-- Equivalently, the list of allocated object identifiers has no duplicates. -/
theorem boundObject_ids_nodup {model : Model} {snapshot : Instance} {target : Snapshot}
    (h : bindInstance model snapshot = .ok target) :
    (target.objects.map ObjectDecl.id).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j bi bj hij heq
  have bi' : i < target.objects.length := by simpa using bi
  have bj' : j < target.objects.length := by simpa using bj
  have hi := boundObject_id_eq_index h
    (List.getElem?_eq_some_iff.mpr ⟨bi', rfl⟩)
  have hj := boundObject_id_eq_index h
    (List.getElem?_eq_some_iff.mpr ⟨bj', rfl⟩)
  have heq' : target.objects[i].id = target.objects[j].id := by simpa using heq
  have : i = j := ObjectId.mk.inj (hi.symm.trans (heq'.trans hj))
  omega

end VLMOF.Source
