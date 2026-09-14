#!/usr/bin/env bash
# Fetch exact, unmodified public inputs used by the S3 audit.
# Usage: ./experiments/cases/fetch-public-cases.sh /absolute/empty/destination
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: $0 /absolute/empty/destination" >&2
  exit 64
fi

destination=$1
case "$destination" in
  /*) ;;
  *) echo "destination must be absolute" >&2; exit 64 ;;
esac
if [ -e "$destination" ]; then
  echo "refusing to overwrite existing destination: $destination" >&2
  exit 73
fi

train_url=https://github.com/FTSRG/trainbenchmark.git
train_commit=6490047d7449f9a4b66cec032b9377bfc06a54d2
compare_url=https://github.com/eclipse-emf-compare/emf-compare.git
compare_commit=9f25a964c1be423373587d8063a5b132714ebeae

mkdir -p "$destination"
git clone --no-checkout "$train_url" "$destination/trainbenchmark"
git -C "$destination/trainbenchmark" checkout --detach "$train_commit"
git clone --no-checkout "$compare_url" "$destination/emf-compare"
git -C "$destination/emf-compare" checkout --detach "$compare_commit"

cd "$destination"
printf '%s  %s\n' \
  617a0e47ff6a00bf25725544583c45920d3cfb1ca547c1244baf2caa2d63d49a \
  trainbenchmark/trainbenchmark-format-emf-model/src/railway.xcore | sha256sum -c -
printf '%s  %s\n' \
  cb8b07fc6829fb45dd0885ee523a88791c1397d43675fc33c56f267b388ec138 \
  trainbenchmark/models/railway-batch-1.xmi | sha256sum -c -
printf '%s  %s\n' \
  22ab8de30fd5b1ddf0d9cef146db98520cb7a799994f5476b3015dc554e2d8f8 \
  emf-compare/plugins/org.eclipse.emf.compare/model/compare.ecore | sha256sum -c -

git -C "$destination/trainbenchmark" status --porcelain
git -C "$destination/emf-compare" status --porcelain
