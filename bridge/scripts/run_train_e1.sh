#!/usr/bin/env bash
# Reproduce the explicit Train E1 adaptation; originals are never modified.
set -euo pipefail
if [ "$#" -ne 2 ]; then echo "usage: $0 PINNED_TRAIN_CHECKOUT OUTPUT_DIR" >&2; exit 64; fi
train=$1; out=$2; mkdir -p "$out"
bridge=$(cd "$(dirname "$0")/.." && pwd)
checker=/home/xoruser/msc-5/repo/Lean4MDE/VL-MOF/.lake/build/bin/vlmof
xcore="$train/trainbenchmark-format-emf-model/src/railway.xcore"
test -f "$out/railway.generated.ecore" || mvn -q -f "$bridge/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.XcoreToEcore -Dexec.args="$xcore $out/railway.generated.ecore"
test -f "$out/railway.profile.ecore" || mvn -q -f "$bridge/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.StripEcoreAnnotations -Dexec.args="$out/railway.generated.ecore $out/railway.profile.ecore"
for stem in railway-batch-1 railway-batch-2 railway-inject-1 railway-inject-2 railway-repair-1 railway-repair-2; do
  test -f "$out/$stem.adapted.xmi" || python3 "$bridge/scripts/adapt_train_defaults.py" "$train/models/$stem.xmi" "$out/$stem.adapted.xmi" "$out/$stem.manifest.json"
  test -s "$out/$stem.e1.json" || mvn -q -f "$bridge/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange -Dexec.args="import $out/railway.profile.ecore -- $out/$stem.adapted.xmi" > "$out/$stem.e1.json"
  test -s "$out/$stem.check.json" || /usr/bin/time -f 'user=%U elapsed=%e maxRSS=%M' -o "$out/$stem.check.time" "$checker" check-json "$out/$stem.e1.json" > "$out/$stem.check.json"
done
sha256sum "$xcore" "$out/railway.generated.ecore" "$out/railway.profile.ecore" "$out"/*.adapted.xmi "$out"/*.e1.json > "$out/SHA256SUMS"
