#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly challenge_dir="Challenge/Blake2f"
readonly challenge_module="Challenge.Blake2f"
readonly challenge_display="BLAKE2f"
readonly scorer_exe="blake2fchallenge"

source scripts/lib/check-hash-submissions.sh

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
