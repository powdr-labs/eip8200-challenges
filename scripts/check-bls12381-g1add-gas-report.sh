#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly report_script_path="scripts/report-bls12381-g1add-gas.sh"
readonly challenge_dir="Challenge/Bls12381G1Add"
readonly challenge_display="BLS12-381 G1ADD"
readonly marker_id="BLS12381G1ADD"

source scripts/lib/check-hash-gas-report.sh

check_hash_gas_report "$@"
