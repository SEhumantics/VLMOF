#!/usr/bin/env bash
# Reproduce the explicit Train E1 adaptation; originals are never modified.
set -euo pipefail
if [ "$#" -ne 2 ]; then echo "usage: $0 PINNED_TRAIN_CHECKOUT OUTPUT_DIR" >&2; exit 64; fi
train=$(realpath "$1"); out=$(realpath -m "$2")
test "$(git -C "$train" rev-parse HEAD)" = 6490047d7449f9a4b66cec032b9377bfc06a54d2 || { echo "unexpected Train revision" >&2; exit 65; }
mkdir "$out" # Require a new result directory; never erase prior evidence.
bridge=${BRIDGE:-$(cd "$(dirname "$0")/.." && pwd)}
repo=$(cd "$bridge/.." && pwd)
checker=${CHECKER:-$repo/.lake/build/bin/vlmof}
test -x "$checker"
mvn -q -f "$bridge/pom.xml" test-compile
xcore="$train/trainbenchmark-format-emf-model/src/railway.xcore"
mvn -q -f "$bridge/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.XcoreToEcore -Dexec.args="$xcore $out/railway.generated.ecore"
mvn -q -f "$bridge/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.StripEcoreAnnotations -Dexec.args="$out/railway.generated.ecore $out/railway.profile.ecore $xcore $out/railway.profile.manifest.json"
for stem in railway-batch-1 railway-batch-2 railway-inject-1 railway-inject-2 railway-repair-1 railway-repair-2; do
  python3 "$bridge/scripts/adapt_train_defaults.py" "$train/models/$stem.xmi" "$out/$stem.adapted.xmi" "$out/$stem.manifest.json"
  mvn -q -f "$bridge/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange -Dexec.args="import $out/railway.profile.ecore -- $out/$stem.adapted.xmi" > "$out/$stem.e1.json"
  /usr/bin/time -f 'user=%U elapsed=%e maxRSS=%M' -o "$out/$stem.check.time" "$checker" check-json "$out/$stem.e1.json" > "$out/$stem.check.json"
done
sha256sum "$xcore" "$out/railway.generated.ecore" "$out/railway.profile.ecore" "$out"/*.adapted.xmi "$out"/*.e1.json > "$out/SHA256SUMS"
