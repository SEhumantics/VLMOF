# Train route and switch-position case

The main example is an authored, structural projection of the pinned Train
Benchmark v1.0 Xcore. It is small enough to read in full while retaining
inheritance, an enumeration, a lower-bounded reference, two opposite pairs, and composite
containment. It demonstrates conformance to the selected structural EMOF
profile. It does not execute Train queries, transformations, or the benchmark.

## Provenance

The published source is Gábor Szárnyas, Benedek Izsó, István Ráth, and Dániel
Varró, “The Train Benchmark: cross-technology performance evaluation of
continuous model queries,” *Software & Systems Modeling* 17, 1365–1393 (2018),
[doi:10.1007/s10270-016-0571-8](https://doi.org/10.1007/s10270-016-0571-8).
The paper presents the domain and metamodel on printed pages 1367–1369, Figures
1–3. The article is CC BY 4.0.

The artifact is the upstream `v1.0` tag, commit
`6490047d7449f9a4b66cec032b9377bfc06a54d2`, under EPL-1.0. Its original
[`railway.xcore`](https://github.com/FTSRG/trainbenchmark/blob/6490047d7449f9a4b66cec032b9377bfc06a54d2/trainbenchmark-format-emf-model/src/railway.xcore)
has SHA-256 `617a0e47ff6a00bf25725544583c45920d3cfb1ca547c1244baf2caa2d63d49a`.
The `.dsl` files below are newly authored translations; they are not upstream
Train notation or data.

## Original and translated notation

The original Xcore declarations corresponding to the central relation are:

```text
class Route extends RailwayElement {
    boolean active
    contains SwitchPosition[] follows opposite route
    refers Sensor[2..*] requires
}

class Switch extends TrackElement {
    Position currentPosition
    refers SwitchPosition[] positions opposite target
}

class SwitchPosition extends RailwayElement {
    Position position
    refers Route route opposite follows
    refers Switch target opposite positions
}
```

The executable translation spells out bounds and collection flags and gives
the two opposite pairs explicit association declarations:

```text
class Route extends railway::RailwayElement {
  active : Boolean [0..1] ordered unique;
  follows : railway::SwitchPosition [0..*] ordered unique composite;
  requires : railway::Sensor [2..*] ordered unique;
}

association RouteFollows {
  ends railway::Route::follows, railway::SwitchPosition::route;
}
```

The translation uses an explicit `railway` package. The pinned v1.0 Xcore `[]`
shorthand means `[0..*]`; unmarked scalar features use `[0..1]`. The translated `ordered`
and `unique` flags follow the usual Ecore defaults. On upper-one features these
flags do not change the admitted occurrence lists. `RailwayElement.id` remains
an ordinary Integer property: the translation deliberately omits the DSL's
`(id)` marker.

## Selected fragment

| Train declaration | Translation | Reason retained |
|---|---|---|
| `Position` | enumeration with all three literals | Exercises enumeration typing and makes default-sensitive values explicit. |
| `RailwayElement.id` | inherited optional Integer property | Separates domain data from object identity and EMOF `isID`. |
| `TrackElement`, `Switch` | abstract superclass and concrete subclass | Retains the published inheritance path. |
| `Route.active` | optional Boolean property | Exercises an explicitly present Boolean scalar. |
| `Route.requires` | ordered unique reference with lower bound two | Gives a direct multiplicity consequence. |
| `Route.follows` / `SwitchPosition.route` | composite forward end and upper-one opposite | Gives containment plus reciprocal incidence. |
| `Switch.positions` / `SwitchPosition.target` | many-to-upper-one opposite pair | Gives a second reciprocal relation used by the domain narrative. |
| `Switch.currentPosition`, `SwitchPosition.position` | optional `Position` values | Records the state used by Train's separate `SwitchSet` query without encoding that query as structural conformance. |

The projection omits `RailwayContainer`, `Region`, `Segment`, `Semaphore`, the
`Signal` enumeration, `routes`, `regions`, `sensors`, `elements`, `monitors`,
`monitoredBy`, `connectsTo`, `entry`, `exit`, `semaphores`, and all generator
annotations. These deletions make this a named projection, not an import of the
complete Train metamodel. No retained declaration is weakened relative to
**pinned v1.0 Xcore**. Figure 2(a) of the published paper instead labels
`SwitchPosition.route` and `.target` as `1`. The v1.0 Xcore and its generated
Ecore make them `0..1`; thus the v1.0 projection is weaker at those ends than
the printed diagram. The separate
[`route-switch-published.dsl`](../examples/train/route-switch-published.dsl)
uses `[1..1]` for both, preserving the displayed paper bounds. It remains an
authored structural projection, and the paper does not label scalar attribute
bounds. [The example guide](../examples/train/README.md) distinguishes their
source versions and evaluation roles.

## Authored snapshots and consequences

[`route-switch.dsl`](../examples/train/route-switch.dsl) contains one route, one
switch, their shared switch position, and two sensors. Every applicable
observation is present, including all optional Boolean, Integer, and enumeration
values. This avoids relying on XMI omission or Ecore default materialization.
The objects are authored for this project and are not a subset of an upstream
generated XMI model.

[`invalid-required-sensors.dsl`](../examples/train/invalid-required-sensors.dsl)
changes the route's `requires` observation from two sensors to one. It is rejected
for `multiplicity bounds`. [`invalid-missing-inverse.dsl`](../examples/train/invalid-missing-inverse.dsl)
keeps `route.follows = [switchPosition]` but makes `switchPosition.route = []`.
It is rejected for `opposite counts`. These are structural consequences of the
metamodel mapping.

[`duplicate-ordinary-id.dsl`](../examples/train/duplicate-ordinary-id.dsl) gives
both sensors the integer value 404 and remains structurally accepted. The paper
describes the inherited numeric attribute as a unique identifier (printed page
1368), but the pinned Xcore declaration is plain `int id`, not an Ecore/EMOF ID
property. Global uniqueness would therefore be a separate Train-domain invariant.

The paper's `SwitchSet` query detects an active route whose entry semaphore
shows `GO` while a followed switch differs from its prescribed switch-position
value (printed page 1373, Figure 7d). The projection omits semaphores, so it
cannot state or evaluate that full domain rule. The example sets both position
values to `STRAIGHT` for readability, but acceptance does not establish
`SwitchSet`, the other five Train queries, generator correctness, or railway
safety.

The paired containment end already has an upper bound of one, and both ends are
unique. Repeating the same `SwitchPosition` in `Route.follows` would therefore
be rejected without deciding the broader semantic question of whether two raw
composite occurrences in one parent/role constitute multiple containers.

## Run

From the repository root:

```sh
lake exe vlmof check-dsl examples/train/route-switch.dsl
lake exe vlmof check-dsl examples/train/route-switch-published.dsl
lake exe vlmof check-dsl examples/train/duplicate-ordinary-id.dsl
lake exe vlmof check-dsl examples/train/invalid-required-sensors.dsl
lake exe vlmof check-dsl examples/train/invalid-missing-inverse.dsl
```

The first three report `accepted`. The two files prefixed `invalid-` report
`invalid`, with `multiplicity bounds` and `opposite counts`, respectively.
