# Full Train structural walkthrough

This walkthrough connects the complete pinned v1.0 **structural profile** to the
symbolic notation, Core state, conformance predicate, and a reusable edit theorem.
It does not implement Train queries or establish railway safety.

## Source and representation

Upstream Train v1.0 is commit `6490047d7449f9a4b66cec032b9377bfc06a54d2`;
see [provenance and publication](train-case.md). The retained profile removes one
generator annotation and maps three `EJavaObject` attributes to intended primitive
types. It keeps the executable artifact's bounds. The published diagram instead
requires `route`, `target`, `entry`, and `exit`; the smaller
`route-switch-published.dsl` isolates the first two. Neither historical input nor
measurement has been tightened. The older 2016 Ecore is yet another profile.

[full-v1-batch-1.dsl](../examples/train/full-v1-batch-1.dsl) renders the retained
untouched batch-1 **Core state** as explicit DSL. It is generated research notation,
not upstream Train syntax, a newly authored independent model, or a verified XMI
translation. The source E1 file retains its original provenance/URI mapping.
Its first 61 lines are the full schema; the rest are all 754 objects and 3,378
observations. Enumeration omissions remain empty rows. No defaults are inserted.
The exact-equality test also retains scalar `nonunique` flags from the full profile;
the pedagogic projection uses `unique` at upper-one scalar slots, with the same
admitted occurrence lists. Source display names and all numeric identities match.

| Class (Core ID) | Direct features (Core property IDs) | Superclass |
|---|---|---|
| RailwayElement (0), abstract | id (0) | — |
| RailwayContainer (1) | routes (1), regions (2) | — |
| Region (2) | sensors (3), elements (4) | RailwayElement |
| Route (3) | active (5), follows (6), requires (7), entry (8), exit (9) | RailwayElement |
| Sensor (4) | monitors (10) | RailwayElement |
| TrackElement (5), abstract | monitoredBy (11), connectsTo (12) | RailwayElement |
| Segment (6) | length (13), semaphores (14) | TrackElement |
| Switch (7) | currentPosition (15), positions (16) | TrackElement |
| SwitchPosition (8) | position (17), route (18), target (19) | RailwayElement |
| Semaphore (9) | signal (20) | RailwayElement |

Position has FAILURE/STRAIGHT/DIVERGING; Signal has FAILURE/STOP/GO. These are
literal identities, not a claim to preserve Ecore's numeric enum assignments.
The three explicit opposite pairs are follows/route (6/18), monitors/monitoredBy
(10/11), and positions/target (16/19). Composite properties are routes, regions,
sensors, elements, follows, and semaphores. All 21 declarations appear above,
including inherited features only once under their owning declaration.

## Follow one actual route

Object `o1` is Core object 1, classifier Route (3), with ordinary integer id 3.
It is contained in `o0.routes`; `o1.follows=[@o2]`, `o2.route=[@o1]`, and
`o2.target=[@o32]`. It observes seven required sensors `o25` through `o31`,
entry `o425`, exit `o34`, and `active=[true]`. The full file contains each target,
its inherited observations, and the reciprocal links. These IDs come from the
retained native allocation, not newly inferred domain identifiers.

`Route.requires` becomes declaration 7, lower bound two, with seven reference
occurrences at key (1,7). `SnapshotConforms.bounds` requires their length to meet
that bound. Truncating this row to one sensor preserves typing and all opposites
but fails multiplicity; the test requires exactly that diagnostic.

`Route.active` becomes Boolean declaration 5, upper one. The operation
`toggleBooleanSlot m (ObjectId.mk 1) (PropertyId.mk 5)` maps its `[true]` to
`[false]`. In [Model/Edits.lean](../VLMOF/Model/Edits.lean),
`toggleBooleanSlot_conforms` proves full structural conformance after this edit
for **every** conforming schema/snapshot and any chosen key. The proof does not
assume post-edit conformance or call the checker. Negation preserves Boolean
typing and is injective, so it preserves uniqueness. All lengths, keys, references,
opposite counts, containers and containment paths remain unchanged. Missing keys
or non-Boolean slots are unchanged; optional empty rows stay empty. Repeating the
edit restores the raw snapshot (`toggleBooleanSlot_twice`). This is one bounded
operation, not a repair algorithm, relinking theorem, or reflective service model.

The test's `toggle_accepted` client composes that theorem with `checkSnapshot_iff`:
an accepted input remains accepted. Runtime rechecking is an extra regression
witness, not the reason the universal theorem holds. Changing `active` can affect
Train's SwitchSet query, which additionally depends on entry semaphore and switch
positions. Structural preservation alone therefore does not settle that query.

## Reproduce from repository root (Linux/WSL)

After installing the pinned Lean toolchain, run:

```sh
lake build
CORE=../../../misc/fift-review/evidence/public-raw-alignment-01/normalized/public-train-raw-batch-1-profile.e1.json
python3 scripts/train_walkthrough.py "$CORE" /tmp/full-v1-batch-1.dsl
cmp /tmp/full-v1-batch-1.dsl examples/train/full-v1-batch-1.dsl
lake env lean --run experiments/TrainWalkthrough.lean "$CORE" examples/train/full-v1-batch-1.dsl
python3 scripts/test_cli.py -v
```

The sixth-review companion includes the retained E1 input at this relative path.
A repository-only checkout does not contain the historical input; use the companion
or pass its explicit path. The Lean experiment reparses and elaborates the generated
DSL and compares `Schema` and `Snapshot` by exact decidable equality with the
independently JSON-decoded input. It then checks original acceptance, the actual
Boolean change and acceptance, double-toggle restoration, one-sensor rejection,
and raw empty/repeated/mixed-value edge cases. A mismatch raises a failure.
Parsing, JSON decoding, and the Python renderer are tested boundaries. No general
parser, serializer, XMI importer or representation-coverage theorem is asserted.

## Coverage and interpretation witnesses

| Evidence family | Obligations exercised | Limit |
|---|---|---|
| Full Train v1.0 | inheritance, scalar/enum typing, lower bounds, three opposite pairs, containment, explicit absence | one public positive family; no query semantics |
| Authored stars/chains | inherited features, ordered occurrences, breadth/depth of containment | controlled workloads, not new public families |
| Unique String separator | duplicate occurrence versus generic EMF validator | selected dynamic validator condition only |
| Repeated unpaired composite row | one parent despite repeated same-parent occurrences | native collector revisits; not aligned |
| Distinct parents / reverse roles | reject two parents; reject two active reverse container properties even for one parent | selected static reading of MOF 12.5.5 |
| EMF Compare input | unsupported native feature boundary | no positive validation claim |

The counterpart source clauses and witnesses are in `sources/PROFILE.md` and
`sources/CLAUSE-AUDIT.md`. The historical timing campaign, five process timeouts,
and twelve adapted-default presence differences remain separate evidence.
