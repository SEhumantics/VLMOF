# Two Train structural projections

The [published Train Benchmark paper](https://doi.org/10.1007/s10270-016-0571-8),
Figure 2(a), printed p. 1368, labels the `SwitchPosition.route` and
`SwitchPosition.target` reference ends `1`. Their opposite `Route.follows` and
`Switch.positions` ends are `0..*`. The diagram does not give cardinalities for
scalar attributes.

The separately pinned Train v1.0
[`railway.xcore`](https://github.com/FTSRG/trainbenchmark/blob/6490047d7449f9a4b66cec032b9377bfc06a54d2/trainbenchmark-format-emf-model/src/railway.xcore)
declares scalar `route` and `target` references without a lower bound. Generated
Ecore gives each a lower bound of zero. These sources differ; both projections
below name their basis explicitly.

| Example | Basis | `SwitchPosition.route` / `.target` | Use |
|---|---|---|---|
| [`route-switch.dsl`](route-switch.dsl) | Pinned v1.0 Xcore | `0..1` / `0..1` | Existing five-object example and inherited timed Train projection |
| [`route-switch-published.dsl`](route-switch-published.dsl) | Displayed reference bounds in published Figure 2(a) | `1..1` / `1..1` | Motivating paper-diagram example and a required-reference discriminator |

Both are authored **structural projections**: they retain six of the ten Train
classes and selected properties. Neither is a full Train metamodel or executes
the benchmark queries. The published-diagram variant changes only the two
displayed required reference bounds; it does not assert the scalar bounds of a
separate, older 2016 Ecore version. See [the case guide](../../docs/train-case.md)
for the selected and omitted declarations. The full 10-class v1.0 structural
profile used for public snapshot validation is a distinct experiment.

From the repository root:

```sh
lake exe vlmof check-dsl examples/train/route-switch.dsl
lake exe vlmof check-dsl examples/train/route-switch-published.dsl
python3 -m unittest scripts.test_cli.DslCommandTests.test_train_published_reference_bounds
```

The test removes both ends of each opposite pair, preserving inverse
consistency. v1.0 accepts the empty pair; the published-diagram projection
rejects it for `multiplicity bounds`.
