# Audited public inputs

This directory records a source-only S3 audit. It provides exact public input
pins and a repeatable XML inventory; it does **not** import XMI, run EMF or the
benchmark, or claim EMF Compare compatibility.

## Acquire exact originals

| Case | Origin and revision | Terms at that revision | Checked material |
|---|---|---|---|
| Train Benchmark | `https://github.com/FTSRG/trainbenchmark.git`, tag `v1.0`, detached commit `6490047d7449f9a4b66cec032b9377bfc06a54d2` | repository `LICENSE`: Eclipse Public License 1.0 | `trainbenchmark-format-emf-model/src/railway.xcore` SHA-256 `617a0e47ff6a00bf25725544583c45920d3cfb1ca547c1244baf2caa2d63d49a`; `models/railway-batch-1.xmi` SHA-256 `cb8b07fc6829fb45dd0885ee523a88791c1397d43675fc33c56f267b388ec138` |
| EMF Compare | `https://github.com/eclipse-emf-compare/emf-compare.git`, tag `3.3.28`, detached commit `9f25a964c1be423373587d8063a5b132714ebeae` | repository `LICENSE`: Eclipse Public License 1.0 | `plugins/org.eclipse.emf.compare/model/compare.ecore` SHA-256 `22ab8de30fd5b1ddf0d9cef146db98520cb7a799994f5476b3015dc554e2d8f8` |

`fetch-public-cases.sh` refuses an existing destination, checks out each commit
detached, and verifies those hashes:

```sh
./experiments/cases/fetch-public-cases.sh /absolute/empty/public-cases
```

The Train `models/railway-*.xmi` files are checked-in, synthetic/generated
benchmark inputs; they are not operational railway data. The originals are
never copied or modified by this repository.

## Train Benchmark mapping domain

The source declaration is `trainbenchmark-format-emf-model/src/railway.xcore`
(lines 1–79). It has ten classes (two abstract), two enumerations, single
inheritance, no operations, and Boolean/Integer/enum values. It declares
containment (`routes`, `regions`, `sensors`, `elements`, `follows`,
`semaphores`), lower bound `Route.requires[2..*]`, and these opposites:

* `Route.follows` (containment) ↔ `SwitchPosition.route`;
* `Sensor.monitors` ↔ `TrackElement.monitoredBy`;
* `Switch.positions` ↔ `SwitchPosition.target`.

This is structurally within the candidate EMOF fragment if K0/K1 accepts the
usual Ecore feature premises `ordered=true` and `unique=true`. An E1 adapter
must preserve XMI child order and space-separated-reference order, enforce that
unique-occurrence premise, and validate the declared opposite pairs and bounds.
The six source snapshots contain no serialized reference list with a repeated
target token; that is corpus evidence, not a rule allowing a bridge to collapse
repeated occurrences.

`RailwayElement.id` is a plain Integer attribute (Xcore line 8), not an EMOF
`isID`. A bridge must create its own one-to-one EObject-to-core identity map,
keep this `id` as a value, and never promote it to an object identity/key.

### Raw-input/default boundary

The profile defers default/unset histories. Therefore raw Train XMI is
**unsupported**: it omits enum-valued `SwitchPosition.position` and
`Switch.currentPosition`. A future adapter may make a separately recorded
adaptation that materializes each omission as the Xcore enum's first literal,
`FAILURE`, while retaining the original XMI and a manifest of each insertion.
That adaptation is not a direct import. The inventory proves that, in the six
pinned snapshots, every ordinary `id`, `active`, `length`, and `signal` is
serialized; only `position` and `currentPosition` are absent.

Run the retained standard-library inspector after acquisition:

```sh
python3 experiments/cases/inventory_train_snapshots.py \
  /absolute/public-cases/trainbenchmark \
  /tmp/train-snapshot-inventory.json
diff -u experiments/cases/train-snapshot-inventory.json /tmp/train-snapshot-inventory.json
```

[`train-snapshot-inventory.json`](train-snapshot-inventory.json) is the
committed output for all six snapshots. The script uses only
`xml.etree.ElementTree`; it does not load EMF or mutate inputs.

### Exact expected observations for E1

These observations were derived from source XML, independently of an importer.
After the explicitly permitted default-materialization adaptation, an E1 result
for `railway-batch-1.xmi` must show 754 bridge objects including its root, 753
distinct ordinary Integer `id` values, a one-to-one bridge identity map, child
and reference order retained, all three opposite pairs mutually consistent,
one containment parent for every non-root object, and `Route.requires` with at
least two targets. Its six missing `position` and six missing
`currentPosition` values must be documented as inserted `FAILURE` values.
Before that adaptation the same raw input must be reported as unsupported.

| Snapshot | Objects / distinct ordinary IDs | missing `position` / `currentPosition` | reference lists / repeated-target lists |
|---|---:|---:|---:|
| `batch-1` | 754 / 753 | 6 / 6 | 1,374 / 0 |
| `batch-2` | 2,389 / 2,388 | 29 / 29 | 4,376 / 0 |
| `inject-1` | 927 / 926 | 11 / 10 | 1,693 / 0 |
| `inject-2` | 3,407 / 3,406 | 39 / 37 | 6,255 / 0 |
| `repair-1` | 1,418 / 1,417 | 15 / 16 | 2,599 / 0 |
| `repair-2` | 2,687 / 2,686 | 29 / 29 | 4,924 / 0 |

Repeated-value/link behavior remains an adversarial E1 case because these
inputs do not exercise it.

## EMF Compare rejection boundary

The actual pinned model is
`plugins/org.eclipse.emf.compare/model/compare.ecore` (lines 4–444). The full
model is a **rejection case**, not a positive compatibility case: it has 11
classes, four enums, three custom EDataTypes, 12 operations, derived/transient
features, Java/runtime datatypes (`EIterable`, `IEqualityHelper`, `Diagnostic`,
`EJavaObject`) and external Ecore reflective/runtime types (`EObject`,
`EResource`, `EReference`, `EAttribute`). Operations and merge behavior,
derived/read-only/transient behavior, custom Java values, generic operation
types, and Ecore reflection are outside the structural profile.

A later E1 adapter should reject this original model with diagnostics before
decoding. A separately named projection containing only selected declarative
classes, containment, bounds, enums and opposites could test a bounded
structural subcase, but it would be an adaptation and cannot be presented as
EMF Compare import, comparison, or merge support.
