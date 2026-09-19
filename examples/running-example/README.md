# Running example M_T and the Section 3 counterexamples

`mt.dsl` is the paper's running snapshot M_T (Figure 2; object `r` is Figure 3).
Its route, two sensors, switch position and switch are the five objects. Its schema
is the pinned Train v1.0 structural profile, the same 62 lines that open
[`../train/full-v1-batch-1.dsl`](../train/full-v1-batch-1.dsl). Every applicable
property has a row, including the empty `entry` and `exit` rows.

Each other file changes M_T in one place to illustrate one sentence of Section 3.
Rejections name the violated condition through the checker's diagnostic field.

| File | Change to M_T | Paper (Section 3.2) | `check-dsl` result |
|---|---|---|---|
| `mt.dsl` | none | running example | accepted |
| `c2-sw-no-id.dsl` | delete `sw`'s `id` row | C2 alone | invalid: `observations exact` |
| `c4-bounds-drop-sB.dsl` | remove `sB`, so `requires` has one sensor | C4 alone | invalid: `multiplicity bounds` |
| `c5-clear-sp-route.dsl` | `sp.route = []` | C5: 0 ≠ 1 | invalid: `opposite counts` |
| `c5-mixed-follows-twice.dsl` | `follows` nonunique, `[@sp, @sp]`; `route` stays `[@r]` | C5 rejects mixed uniqueness (2 ≠ 1) | invalid: `opposite counts` |
| `c5-mixed-both-twice.dsl` | as above, and `route = [@r, @r]` | control: counts agree | invalid: `multiplicity bounds`, `unique occurrences` |
| `ctl-region-once.dsl` | add region `reg` containing segment `seg` | control | accepted |
| `c4-unique-seg-twice.dsl` | `reg.elements = [@seg, @seg]` | one parent; only C4 uniqueness rejects | invalid: `unique occurrences` |
| `ctl-seg-twice-nonunique.dsl` | as above with `elements` nonunique | accepted without uniqueness | accepted |
| `c6-two-regions.dsl` | `seg` in the `elements` of two regions | C6 alone | invalid: `one container and active container property` |
| `zero-zero-active.dsl` | `active` becomes `[0..0]` and empty | a `0..0` property stays empty | accepted |

Check one file from the repository root, or all of them through the CLI tests:

```sh
lake exe vlmof check-dsl examples/running-example/c4-bounds-drop-sB.dsl
python3 -m unittest scripts.test_cli.RunningExampleTests -v
```

These are authored illustrations of the predicates, not evidence of fidelity to
the standard. For that argument, see [`sources/CLAUSE-AUDIT.md`](../../sources/CLAUSE-AUDIT.md).

The `.dsl` files use the Train Benchmark v1.0 metamodel, so they are licensed
under the [Eclipse Public License 1.0](../../LICENSES/EPL-1.0.txt), like
`examples/train/`. See [NOTICE](../../NOTICE).
