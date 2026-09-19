# Reproducing the evaluation

This guide rebuilds VL-MOF from a clean Linux or WSL machine, reruns every phase
of the paper's evaluation, and checks the results against the printed tables. It
explains what a fresh run can reproduce and what it cannot. For what each result
means, read the [paper map](docs/paper-map.md). For the inputs and the measurement
protocol, read the [evaluation guide](experiments/README.md).

## What a fresh run can and cannot show

- **Proofs** are rechecked in full by `lake build`.
- **Decisions and loaded-state comparisons** (Table 1), and the object and row counts of Table 2, are deterministic. A fresh run should reproduce them exactly.
- **Times** (Table 2) are new observations on your machine. They will differ from the printed values. Report them separately and never substitute them for the paper's numbers.
- **The printed numbers themselves** come from evidence recorded on 15 Sep 2026 that is *not* in this checkout. You can recompute Tables 1 and 2 from that evidence. You cannot rebuild the exact measured binaries, because the timing run used a working tree with uncommitted changes and its generation sources were not hashed (paper, Section 6). See [Companion evidence](#companion-evidence).
- **Public inputs** (Train Benchmark, EMF Compare) and the OMG specification files are downloaded at pinned revisions and verified by hash; they are not in this repository.

## 1. Prerequisites

The versions below were used for the paper's runs and for testing this guide
(Ubuntu 24.04 on WSL2, kernel 6.6, x86-64).

| Tool | Version | Needed for |
|---|---|---|
| Python | ≥ 3.10 (tested 3.12.3), standard library only | all runners |
| Git, GNU Make, curl, `sha256sum` | any recent | sources, public inputs |
| elan with Lean | toolchain pinned in `lean-toolchain`: `leanprover/lean4:v4.33.1` | build, proofs, checker |
| Java | OpenJDK 21 (tested 21.0.12) | EMF bridge |
| Maven | ≥ 3.9 (tested 3.9.16); the wrapper uses `MAVEN_ARGS`, introduced in 3.9 | EMF bridge |
| TeX Live 2023 with `latexmk` | optional | rebuilding the paper |
| Poppler `pdftotext` | optional | `make text` |

On Ubuntu 24.04, install everything except Lean and Maven from the distribution:

```bash
sudo apt-get install -y git make curl python3 openjdk-21-jdk-headless
```

Ubuntu 24.04 packages Maven 3.8, so install the tested Maven release from Apache
and verify it:

```bash
curl -fLO https://archive.apache.org/dist/maven/maven-3/3.9.16/binaries/apache-maven-3.9.16-bin.tar.gz
curl -fL https://archive.apache.org/dist/maven/maven-3/3.9.16/binaries/apache-maven-3.9.16-bin.tar.gz.sha512 -o maven.sha512
echo "$(cat maven.sha512)  apache-maven-3.9.16-bin.tar.gz" | sha512sum -c -
```

```bash
mkdir -p ~/.local/share && tar -xzf apache-maven-3.9.16-bin.tar.gz -C ~/.local/share
```

```bash
export PATH="$HOME/.local/share/apache-maven-3.9.16/bin:$PATH"
```

Install elan without a default toolchain, then the pinned Lean toolchain:

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
```

```bash
elan toolchain install leanprover/lean4:v4.33.1
```

### Measured resources

These were measured on the test machine: 16 logical CPUs (Intel i5-14400F),
20 GB RAM, and a fast network. Downloads depend on your network.

| Item | Disk | Time |
|---|---|---|
| Lean toolchain | 2.9 GB | download-dependent |
| OMG specification files (`make sources`) | 10 MB | 3 s |
| Maven dependencies in an empty local repository | 104 MB | 142 s (2,622 downloads) |
| Public Train/EMF Compare checkouts | 493 MB | 32 s |
| Lean build from scratch (`lake build`, 65 jobs) | 264 MB in `.lake` | 12 s; `validationBench` 1 s |
| Correctness phase, including the EMF comparison | 13 MB of evidence | 3 min |
| Public phase | 34 MB of evidence | 7.5 min (public runner 3.6 min, full Train walkthrough 3.3 min) |
| Timing phase (45 paired trials) | 100–120 MB of evidence | 28–31 min |

Most of the timing phase is the five deep-chain trials, which each wait out the
120-second limit.

## 2. Get the source

```bash
git clone https://github.com/SEhumantics/VLMOF.git VL-MOF
cd VL-MOF
```

Check out the commit you intend to evaluate and record it. All later commands
run from the repository root.

## 3. Network steps (explicit, once)

Nothing after this section downloads anything. Choose one directory for
downloaded inputs and one for results, both outside the repository:

```bash
export INPUTS="$HOME/vlmof-inputs" RUNS="$HOME/vlmof-runs"
```

**Standards sources.** This fetches the six pinned OMG files into `sources/raw/`
(ignored by Git) and verifies their SHA-256 digests. `make verify` rechecks them
offline at any time.

```bash
make sources
```

**Maven dependencies.** This resolves the bridge's dependencies into `~/.m2`, compiles
the bridge, prints the dependency tree and runs the resource-loading probe. The
probe prints `LOADED … marks=[7, 7, 9] reciprocal=true inherited=baseCode`.

```bash
mvn -f bridge/pom.xml test-compile dependency:tree exec:java
```

The EMF, Xcore and Jackson versions are pinned in `bridge/pom.xml`. Xcore's
transitive Xtext/Eclipse dependencies are resolved through version ranges. On
19 Sep 2026 the resolved tree was identical to the one recorded with the paper's
evidence, 59 artifacts. Compare yours with the `maven-dependency-tree` log of a run.

**Public inputs.** The script refuses an existing destination, checks out the
pinned commits detached, and verifies the three evaluated files:

```bash
./experiments/cases/fetch-public-cases.sh "$INPUTS/public-cases"
```

| Input | Revision | Verified file and SHA-256 |
|---|---|---|
| Train Benchmark, tag `v1.0` | `6490047d7449f9a4b66cec032b9377bfc06a54d2` | `railway.xcore` `617a0e47…d63d49a`; `models/railway-batch-1.xmi` `cb8b07fc…8ec138` |
| EMF Compare, tag `3.3.28` | `9f25a964c1be423373587d8063a5b132714ebeae` | `plugins/org.eclipse.emf.compare/model/compare.ecore` `22ab8de3…54d2e8f8` |

Both repositories are EPL-1.0. Full digests are in the script and in
[`experiments/cases/README.md`](experiments/cases/README.md).

## 4. Build and check

```bash
make check
lake build validationBench
```

`make check` does six things:

- verifies the OMG files;
- runs the Python unit tests;
- builds the library, examples and CLI (`lake build`);
- compiles `experiments/ProofClient.lean`, which prints the axioms of its three results;
- compiles `experiments/PaperMap.lean`, which checks every Lean name in the [paper map](docs/paper-map.md) and prints that Theorems 1 and 2 use only `propext`, `Classical.choice` and `Quot.sound`;
- runs the CLI tests, including the running example and Section 3's counterexamples.

## 5. Run the evaluation with the wrapper

[`experiments/reproduce.py`](experiments/reproduce.py) runs the existing runners in
a fixed order. It checks prerequisites first and creates nothing if one is missing.
It then records into one new directory:

- every command with its arguments, exit status and duration;
- stdout and stderr logs, each with its SHA-256;
- tool versions, the repository commit and its `git status`;
- the machine (CPU, memory, load average).

It never downloads anything. Maven runs with `--offline`, and the Lean toolchain
and public checkouts must already exist. Check prerequisites without creating
anything:

```bash
python3 experiments/reproduce.py --check-only --output "$RUNS/check" --phase build --phase correctness
```

Run the non-timing phases in one go:

```bash
python3 experiments/reproduce.py --output "$RUNS/run-01" \
  --phase sources --phase build --phase correctness --phase public \
  --train "$INPUTS/public-cases/trainbenchmark" --emf-compare "$INPUTS/public-cases/emf-compare"
```

Then run timing **alone**, in a later invocation, on an otherwise idle machine.
Close editors running a Lean server and do not build anything meanwhile.

```bash
python3 experiments/reproduce.py --output "$RUNS/timing-01" --phase timing
```

The timing phase never builds. It refuses to start unless `lake build --no-build`
confirms the Lean executables are current and the bridge classes are newer than
their sources. It also records the load average and any running build-tool
processes before and after.

| Phase | Runs | Output under `OUTPUT/` |
|---|---|---|
| `sources` | `scripts/sources.py verify` | logs only |
| `build` | `lake build`, `lake build validationBench`, `mvn test-compile` | logs only |
| `correctness` | unit tests, `ProofClient.lean`, `PaperMap.lean`, CLI tests, `experiments/run.py`, `experiments/run_emf_validation.py`, then `evidence.py table1` | `correctness/authored-cli/`, `correctness/emf-comparison/`, `correctness/table1.json` |
| `public` | the steps listed below | `public/…` |
| `timing` | `experiments/run_fifth_evaluation.py` (5 trials, 10 warmups, 30 repetitions), then `evidence.py table2` | `timing/multifamily/`, `timing/table2.json` |

The `public` phase runs these steps in order:

1. Inventories the Train snapshots and compares the result with the committed inventory.
2. Runs `experiments/run_public.py`.
3. Checks that its adapted Train Ecore and XMI are byte-identical to the retained historical inputs.
4. Writes the two Train fixture manifests and runs `run_emf_validation.py` on them.
5. Renders the full Train DSL, compares it with `examples/train/full-v1-batch-1.dsl`, and runs `experiments/TrainWalkthrough.lean`.
6. Runs `evidence.py table1` (`public/table1.json`).

`OUTPUT/SUMMARY.md` lists every step's status; `OUTPUT/reproduce.json` holds the
details. The wrapper exits 0 only if every step passed. `--trials`, `--warmups`
and `--repetitions` can shorten a trial run of the timing phase. The run then
records `"paper_protocol": false`, and its times are not comparable with Table 2.

## 6. Run the evaluation without the wrapper

The wrapper adds no evaluation logic. These are the runners it calls. Build first
(section 4) and compile the bridge with `mvn -q -f bridge/pom.xml test-compile`.
The runners call `mvn exec:java`, which does not compile.

```bash
python3 experiments/run.py --output "$RUNS/manual/authored-cli"
python3 experiments/run_emf_validation.py --output "$RUNS/manual/emf-comparison"
```

`run_emf_validation.py` selects every fixture in `experiments/cases/emf-validation/`
whose inputs are inside the repository: 17 fixtures. It lists
`train-batch-1-profile.fixture.json` as not selected, because that manifest names
retained inputs in the author's workspace; pass it with `--fixture` when those
inputs are present.

The public import and round trips:

```bash
CHECKER="$PWD/.lake/build/bin/vlmof" python3 experiments/run_public.py \
  --train "$INPUTS/public-cases/trainbenchmark" --emf-compare "$INPUTS/public-cases/emf-compare" \
  --output "$RUNS/manual/public-runner"
```

For the two Train rows of Table 1, write two fixture manifests naming the profile
Ecore from the public runner. One names the adapted XMI with explicit defaults; the
other names the untouched public XMI. Then run the comparison on both:

```bash
F="$RUNS/manual/train-fixtures"; P="$RUNS/manual/public-runner"; mkdir -p "$F"
printf '{"id": "train-batch-1-profile", "ecore": ["%s"], "xmi": ["%s"], "expected": {}, "timing_eligible": false}\n' \
  "$P/artifacts/railway.profile.ecore" "$P/cases/railway-batch-1/adapted.xmi" > "$F/train-batch-1-profile.fixture.json"
printf '{"id": "public-train-raw-batch-1-profile", "ecore": ["%s"], "xmi": ["%s"], "expected": {"emf": "accepted", "vlmof": "accepted"}, "timing_eligible": false}\n' \
  "$P/artifacts/railway.profile.ecore" "$INPUTS/public-cases/trainbenchmark/models/railway-batch-1.xmi" \
  > "$F/public-train-raw-batch-1-profile.fixture.json"
python3 experiments/run_emf_validation.py --output "$RUNS/manual/train-emf-comparison" \
  --fixture "$F/train-batch-1-profile.fixture.json" --fixture "$F/public-train-raw-batch-1-profile.fixture.json"
```

The expectations match the historical manifests. The explicit-defaults case is
unscored, because its loaded states are known to differ. Render and check the full
Train DSL from the untouched import:

```bash
CORE="$RUNS/manual/train-emf-comparison/normalized/public-train-raw-batch-1-profile.e1.json"
python3 scripts/train_walkthrough.py "$CORE" "$RUNS/manual/full-v1-batch-1.dsl"
cmp "$RUNS/manual/full-v1-batch-1.dsl" examples/train/full-v1-batch-1.dsl
lake env lean --run experiments/TrainWalkthrough.lean "$CORE" examples/train/full-v1-batch-1.dsl
```

The timing campaign, on an idle machine after building:

```bash
python3 experiments/run_fifth_evaluation.py --output "$RUNS/manual/timing"
```

It first regenerates the nine synthetic fixtures into `OUTPUT/generated-fixtures/`
and stops unless they are byte-identical to the committed ones. It then runs the
correctness gate and the 45 paired trials. It exits 1 if any trial is incomplete,
which the paper's protocol expects for the 501-deep chain.

## 7. Read and validate the results

```bash
python3 experiments/evidence.py table1 "$RUNS/run-01/correctness/emf-comparison/results.json" \
  "$RUNS/run-01/public/train-emf-comparison/results.json"
python3 experiments/evidence.py table2 "$RUNS/timing-01/timing/multifamily"
```

`table1` prints each fixture's EMF schema and instance decisions, the VL-MOF
decision and the loaded-state comparison. It compares them with Table 1 as parsed
from `paper/sections/evaluation.tex`, and exits 1 if any fixture disagrees.
`table2` recomputes the median of the five process medians for each workload.
It prints the result beside the printed values and counts complete paired trials,
40 of 45 in the paper. It fails only if objects, rows or the trial schedule differ;
times are not compared.

Each runner's `results.json` is the structured record. The EMF, public and timing
runners keep every process's stdout and stderr in `commands/`; `run.py` keeps them
inside `results.json`. The wrapper's summary and its
[meaning](experiments/README.md#outcomes-and-failures) are in the evaluation guide.

## Why every output path must be new

Each runner, the fetch script and the wrapper refuse an existing output path. They
never delete, merge or resume a run. A result directory is therefore one complete
or visibly partial record of one execution. A repeated run cannot silently replace
earlier evidence, and an interrupted run is never mistaken for a finished one. The
wrapper also refuses paths inside the repository, so evidence cannot be committed
by accident. Choose a new name for every attempt, for example `run-02`.

## Companion evidence

The printed tables were computed from five retained evidence collections, about
146 MB and 1,583 files. They are listed with per-collection tree digests and key-file
hashes in [`experiments/companion-evidence.json`](experiments/companion-evidence.json).
They are not in this repository; obtain them from the authors or the companion
archive. With the collections unpacked side by side under `ROOT`:

```bash
python3 experiments/evidence.py companion ROOT
python3 experiments/evidence.py table1 ROOT/multifamily-evaluation-03/correctness/results.json \
  ROOT/public-raw-alignment-01/results.json
python3 experiments/evidence.py table2 --exact ROOT/multifamily-evaluation-03
```

With `--exact`, `table2` requires the printed times, recomputed from the raw samples.
The records are unedited. They contain absolute paths of the author's workspace,
and one host name in a `uname` log; see the manifest's `notes`. The upstream
checkouts used by those runs are not redistributed: recreate them with
`fetch-public-cases.sh ROOT/public-cases-01`. The collections contain data derived from the
Train Benchmark, so a published archive must carry the EPL-1.0 text and the
Train Benchmark notice from [`NOTICE`](NOTICE).

## Remaining limits

- A fresh timing run measures a different build and machine state. Compare its times with Table 2 only as a separate observation.
- The paper's timing and correctness runs used commit `7ed9709` with uncommitted changes, recorded in their `git-dirty` logs. The third-review public inputs came from a commit that is not in the current history. Their Ecore and XMI bytes are what matters, and the `public` phase checks that a fresh adaptation reproduces them.
- Three chain fixture manifests changed after the timing run, in metadata only; see the manifest's `notes`. A fresh run therefore records different hashes for those three files.
- Ten warmups do not establish JIT stabilization for the JVM.
