#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 1 ]; then echo "usage: $0 TRAIN_E1_OUTPUT_DIR" >&2; exit 64; fi
input=$(realpath "$1"); review=${BRIDGE:-$(cd "$(dirname "$0")/.." && pwd)}
repo=$(cd "$review/.." && pwd); checker=${CHECKER:-$repo/.lake/build/bin/vlmof}
out="$input/roundtrip-review"; mkdir "$out"
mvn -q -f "$review/pom.xml" test-compile
for stem in railway-batch-1 railway-batch-2 railway-inject-1 railway-inject-2 railway-repair-1 railway-repair-2; do
  dir="$out/$stem"; mkdir -p "$dir"
  mvn -q -f "$review/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange -Dexec.args="export $input/$stem.e1.json $dir/railway.ecore $dir/railway.xmi"
  mvn -q -f "$review/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange -Dexec.args="import $dir/railway.ecore -- $dir/railway.xmi" > "$dir/reloaded.e1.json"
  mvn -q -f "$review/pom.xml" exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange -Dexec.args="compare $input/$stem.e1.json $dir/reloaded.e1.json $dir/railway.xmi.ids.json" > "$dir/compare.txt"
  /usr/bin/time -f 'user=%U elapsed=%e maxRSS=%M' -o "$dir/check.time" "$checker" check-json "$dir/reloaded.e1.json" > "$dir/check.json"
done
sha256sum "$out"/*/* > "$out/SHA256SUMS"
