#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly report_script_path="scripts/report-blake2f-gas.sh"
readonly challenge_dir="Challenge/Blake2f"
readonly challenge_display="BLAKE2f"
readonly marker_id="BLAKE2F"

source scripts/lib/check-hash-gas-report.sh

check_hash_gas_report "$@"
