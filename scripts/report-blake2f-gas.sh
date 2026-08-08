#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

cd "$(git rev-parse --show-toplevel)"

readonly challenge_dir="Challenge/Blake2f"
readonly challenge_module="Challenge.Blake2f"
readonly challenge_display="BLAKE2f"
readonly challenge_slug="blake2f"
readonly marker_id="BLAKE2F"
readonly report_script_path="scripts/report-blake2f-gas.sh"
readonly scorer_exe="blake2fchallenge"
readonly expected_rows=26

source scripts/lib/check-hash-submissions.sh

declare -a implementation_names=("Reference")
declare -a implementation_links=("Reference/")
declare -a artifact_paths=("$challenge_dir/Reference/reference.hex")
declare -a gas_files=("$challenge_dir/Reference/Proofs/Gas.lean")
declare -a gas_modules=("$challenge_module.Reference.Proofs.Gas")
declare -a bytecode_names=("$challenge_module.referenceBytecode")
declare -a formula_names=("$challenge_module.Reference.Proofs.Gas.gasFormula")
declare -a schedule_names=("$challenge_module.Reference.Proofs.Gas.gasSchedule")
declare -a schedule_theorems=("$challenge_module.Reference.Proofs.Gas.gasSchedule_correct")
reference_clean_total=""
reference_dirty_total=""

readonly report_labels=(
  "0 rounds f=0"
  "1 round"
  "12 rounds f=0"
  "12 rounds f=1"
  "100 rounds"
  "212-byte invalid"
  "flag=2 invalid"
)

discover_submissions() {
  local submission_dir
  for submission_dir in "$submission_root"/*; do
    [[ -d "$submission_dir" ]] || continue
    local name
    name="$(basename "$submission_dir")"
    if [[ ! "$name" =~ ^[A-Z][A-Za-z0-9_]*$ ]]; then
      printf 'error: submission directory %s is not an UpperCamelCase Lean identifier\n' \
        "$name" >&2
      return 1
    fi
    if [[ ! -f "$submission_dir/bytecode.hex" ]]; then
      printf 'error: %s is missing bytecode.hex\n' "$submission_dir" >&2
      return 1
    fi
    local module="$module_prefix.$name"
    implementation_names+=("$name")
    implementation_links+=("Submissions/$name/")
    artifact_paths+=("$submission_dir/bytecode.hex")
    gas_files+=("$submission_dir/Gas.lean")
    gas_modules+=("$module.Gas")
    bytecode_names+=("$module.bytecode")
    formula_names+=("$module.gasFormula")
    schedule_names+=("$module.gasSchedule")
    schedule_theorems+=("$module.gasSchedule_correct")
  done
}

canonical_hex_size() {
  local path="$1"
  local hex
  hex="$(<"$path")"
  if [[ ! "$hex" =~ ^([0-9a-f][0-9a-f])*$ ]]; then
    printf 'error: %s is not canonical lowercase bytecode hex\n' "$path" >&2
    return 1
  fi
  printf '%s' "$(( ${#hex} / 2 ))"
}

format_ratio() {
  local numerator="$1"
  local denominator="$2"
  awk -v numerator="$numerator" -v denominator="$denominator" \
    'BEGIN { printf "%.2f×", numerator / denominator }'
}

display_pair() {
  local clean="$1"
  local dirty="$2"
  if [[ "$clean" == "$dirty" ]]; then
    printf '%s' "$clean"
  else
    printf '%s / %s' "$clean" "$dirty"
  fi
}

display_ratio_pair() {
  display_pair "$(format_ratio "$1" "$3")" "$(format_ratio "$2" "$4")"
}

report_measured_row() {
  local index="$1"
  local name="${implementation_names[$index]}"
  local path="${artifact_paths[$index]}"
  local csv
  printf 'measuring Tier-1 gas for %s\n' "$name" >&2
  if ! csv="$(lake exe "$scorer_exe" --hex="$path" --csv)"; then
    printf 'error: Tier-1 scorer rejected %s\n' "$name" >&2
    return 1
  fi

  local -A clean=()
  local -A dirty=()
  local clean_total=0
  local dirty_total=0
  local valid_clean_total=0
  local valid_dirty_total=0
  local precompile_total=0
  local rows=0
  local vector bytes rounds frame status gas
  while IFS=, read -r vector bytes rounds frame status gas; do
    [[ "$vector" == "vector" ]] && continue
    [[ -z "$vector" ]] && continue
    if [[ ! "$status" =~ ^ok ]]; then
      printf 'error: Tier-1 vector %s failed for %s: %s\n' \
        "$vector" "$name" "$status" >&2
      return 1
    fi
    if [[ ! "$gas" =~ ^[0-9]+$ ]]; then
      printf 'error: scorer emitted invalid gas for %s/%s/%s: %s\n' \
        "$name" "$vector" "$frame" "$gas" >&2
      return 1
    fi
    case "$frame" in
      clean)
        clean["$vector"]="$gas"
        clean_total=$((clean_total + gas))
        if [[ "$rounds" =~ ^[0-9]+$ ]]; then
          valid_clean_total=$((valid_clean_total + gas))
          precompile_total=$((precompile_total + rounds))
        fi
        ;;
      dirty)
        dirty["$vector"]="$gas"
        dirty_total=$((dirty_total + gas))
        if [[ "$rounds" =~ ^[0-9]+$ ]]; then
          valid_dirty_total=$((valid_dirty_total + gas))
        fi
        ;;
      *)
        printf 'error: scorer emitted unknown frame %s\n' "$frame" >&2
        return 1
        ;;
    esac
    rows=$((rows + 1))
  done <<< "$csv"

  if [[ "$rows" -ne "$expected_rows" ]]; then
    printf 'error: expected %s Tier-1 rows for %s, got %s\n' \
      "$expected_rows" "$name" "$rows" >&2
    return 1
  fi
  if [[ "$index" -eq 0 ]]; then
    reference_clean_total="$clean_total"
    reference_dirty_total="$dirty_total"
  elif [[ -z "$reference_clean_total" || -z "$reference_dirty_total" ]]; then
    printf 'error: reference gas must be measured before submissions\n' >&2
    return 1
  fi

  printf '| [%s](%s) | %s' "$name" "${implementation_links[$index]}" \
    "$(canonical_hex_size "$path")"
  local label
  for label in "${report_labels[@]}"; do
    if [[ -z "${clean[$label]:-}" || -z "${dirty[$label]:-}" ]]; then
      printf '\nerror: scorer omitted vector %s for %s\n' "$label" "$name" >&2
      return 1
    fi
    printf ' | %s' "$(display_pair "${clean[$label]}" "${dirty[$label]}")"
  done
  printf ' | %s' "$(display_pair "$clean_total" "$dirty_total")"
  printf ' | %s' "$(display_ratio_pair "$valid_clean_total" "$valid_dirty_total" \
    "$precompile_total" "$precompile_total")"
  printf ' | %s |\n' "$(display_ratio_pair "$clean_total" "$dirty_total" \
    "$reference_clean_total" "$reference_dirty_total")"
}

cleanup_files() {
  local file
  for file in "$@"; do
    [[ -e "$file" ]] && rm -f -- "$file"
  done
}

report_proved_row() {
  local index="$1"
  local name="${implementation_names[$index]}"
  local gas_file="${gas_files[$index]}"
  local gas_module="${gas_modules[$index]}"
  local bytecode_name="${bytecode_names[$index]}"
  local formula_name="${formula_names[$index]}"
  local schedule_name="${schedule_names[$index]}"
  local theorem_name="${schedule_theorems[$index]}"

  if [[ ! -f "$gas_file" ]]; then
    printf '1\t0\t%s\t| [%s](%s) | — | Not provided |\n' \
      "$name" "$name" "${implementation_links[$index]}"
    return
  fi

  printf 'checking proved gas schedule for %s\n' "$name" >&2
  local build_output
  if ! build_output="$(lake build "$gas_module" 2>&1)"; then
    printf 'error: gas module failed to build for %s\n%s\n' \
      "$name" "$build_output" >&2
    return 1
  fi

  local proof_check eval_check value_check
  proof_check="$(mktemp "/tmp/$challenge_slug-gas-proof.XXXXXX.lean")"
  eval_check="$(mktemp "/tmp/$challenge_slug-gas-eval.XXXXXX.lean")"
  value_check="$(mktemp "/tmp/$challenge_slug-gas-values.XXXXXX.lean")"
  trap 'cleanup_files "$proof_check" "$eval_check" "$value_check"; trap - RETURN' RETURN

  {
    printf 'import %s\n' "$gas_module"
    printf 'import %s.AdditionalGoals.GasSchedule\n\n' "$challenge_module"
    printf 'example : %s.CorrectWithSchedule %s %s := %s\n\n' \
      "$challenge_module" "$bytecode_name" "$schedule_name" "$theorem_name"
    printf 'example : %s = %s.eval := by rfl\n\n' \
      "$schedule_name" "$formula_name"
    printf '#print axioms %s\n' "$theorem_name"
  } > "$proof_check"

  local lean_output
  if ! lean_output="$(lake env lean "$proof_check" 2>&1)"; then
    printf 'error: proved gas check failed for %s\n%s\n' \
      "$name" "$lean_output" >&2
    return 1
  fi
  if ! check_axiom_output "$theorem_name" "$lean_output"; then
    return 1
  fi

  {
    printf 'import %s\n' "$gas_module"
    printf 'import %s.Scorer\n\n' "$challenge_module"
    printf '#eval IO.println ("GAS_FORMULA," ++ %s.toLatex)\n' "$formula_name"
    printf '#eval IO.println s!"GAS_RANK,{(%s.Scorer.vectors.map ' "$challenge_module"
    printf 'fun vector => %s.eval vector.input).sum}"\n' "$formula_name"
  } > "$eval_check"

  local eval_output
  if ! eval_output="$(lake env lean "$eval_check" 2>&1)"; then
    printf 'error: gas formula is not executable for %s\n%s\n' \
      "$name" "$eval_output" >&2
    return 1
  fi
  local latex=""
  local rank=""
  local line
  while IFS= read -r line; do
    case "$line" in
      GAS_FORMULA,*) latex="${line#GAS_FORMULA,}" ;;
      GAS_RANK,*) rank="${line#GAS_RANK,}" ;;
    esac
  done <<< "$eval_output"
  if [[ -z "$latex" || "$latex" == *'|'* || "$latex" == *'$'* || \
      "$latex" == *$'\t'* ]]; then
    printf 'error: invalid rendered gas formula for %s: %s\n' "$name" "$latex" >&2
    return 1
  fi
  if [[ ! "$rank" =~ ^[0-9]+$ ]]; then
    printf 'error: invalid gas ranking value for %s: %s\n' "$name" "$rank" >&2
    return 1
  fi

  {
    printf 'import %s\n' "$gas_module"
    printf 'import %s.Scorer\n\n' "$challenge_module"
    printf 'example : (%s.Scorer.vectors.map (fun vector => ' "$challenge_module"
    printf '%s.eval vector.input)).sum = %s := by native_decide\n' \
      "$formula_name" "$rank"
  } > "$value_check"
  if ! lean_output="$(lake env lean "$value_check" 2>&1)"; then
    printf 'error: ranked gas value does not kernel-reduce for %s\n%s\n' \
      "$name" "$lean_output" >&2
    return 1
  fi

  printf '0\t%s\t%s\t| [%s](%s) | $`G(I) = %s`$ | [proved](%s) |\n' \
    "$rank" "$name" "$name" "${implementation_links[$index]}" "$latex" \
    "${gas_file#"$challenge_dir/"}"

  cleanup_files "$proof_check" "$eval_check" "$value_check"
  trap - RETURN
}

remove_gas_fixture() {
  local fixture_dir="$1"
  rm -f -- "$fixture_dir/Bytecode.lean" "$fixture_dir/Gas.lean"
  rmdir -- "$fixture_dir"
}

run_axiom_self_test() {
  local name="GasAxiomSelfTest$$"
  local fixture_dir="$submission_root/$name"
  if [[ -e "$fixture_dir" ]]; then
    printf 'error: refusing to overwrite %s\n' "$fixture_dir" >&2
    return 1
  fi
  mkdir -p -- "$fixture_dir"
  {
    printf 'import %s.Reference.Bytecode\n\n' "$challenge_module"
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'def bytecode : ByteArray := %s.referenceBytecode\n\n' "$challenge_module"
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$fixture_dir/Bytecode.lean"
  {
    printf 'import %s.%s.Bytecode\n' "$module_prefix" "$name"
    printf 'import %s.AdditionalGoals.GasSchedule\n\n' "$challenge_module"
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'def gasFormula : %s.GasFormula := 0\n' "$challenge_module"
    printf 'def gasSchedule : ByteArray → Nat := gasFormula.eval\n\n'
    printf 'axiom gasSchedule_correct :\n'
    printf '  %s.CorrectWithSchedule bytecode gasSchedule\n\n' "$challenge_module"
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$fixture_dir/Gas.lean"

  implementation_names=("$name")
  implementation_links=("Submissions/$name/")
  gas_files=("$fixture_dir/Gas.lean")
  gas_modules=("$module_prefix.$name.Gas")
  bytecode_names=("$module_prefix.$name.bytecode")
  formula_names=("$module_prefix.$name.gasFormula")
  schedule_names=("$module_prefix.$name.gasSchedule")
  schedule_theorems=("$module_prefix.$name.gasSchedule_correct")

  local accepted=false
  if report_proved_row 0 >/dev/null; then
    accepted=true
  fi
  remove_gas_fixture "$fixture_dir"
  if [[ "$accepted" == true ]]; then
    printf 'error: gas checker accepted its fake-axiom negative control\n' >&2
    return 1
  fi
  printf 'gas checker negative control: rejected fake proved schedule as expected\n'
}

main() {
  if [[ "${1:-}" == "--self-test" && $# -eq 1 ]]; then
    run_axiom_self_test
    return
  fi
  if [[ $# -ne 0 ]]; then
    printf 'usage: %s [--self-test]\n' "$0" >&2
    return 2
  fi
  discover_submissions

  printf '<!-- BEGIN GENERATED %s GAS REPORT -->\n' "$marker_id"
  printf '## Gas report\n\n'
  printf 'Generated by `%s`; CI checks that this section is current.\n\n' \
    "$report_script_path"
  printf '### Category 1: Tier-1 measured gas\n\n'
  printf '%s\n' \
    'Gas is measured by concrete execution in the pinned EVM semantics.' \
    'A single number means the clean and dirty frames agree; `clean / dirty`' \
    'is shown otherwise. The total covers all 13 public vectors.' \
    'The precompile ratio compares the ten valid-vector totals against the' \
    'EIP-152 round-priced precompile; exceptional inputs are excluded.' \
    'Measurements are tests, not proofs.'
  printf '\n'
  printf '| implementation | bytes | R=0, f=0 | R=1 | R=12, f=0 | R=12, f=1 | R=100 | bad length | bad flag | all vectors | valid vs precompile | vs reference |\n'
  printf '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n'
  local index
  for index in "${!implementation_names[@]}"; do
    report_measured_row "$index"
  done

  printf '\n### Category 2: proved calldata-dependent gas bounds\n\n'
  printf '%s\n' \
    'A proved row supplies a symbolic `gasFormula`, its executable' \
    '`gasSchedule`, and a kernel-checked' \
    '`CorrectWithSchedule bytecode gasSchedule` theorem. The checker requires' \
    '`gasSchedule = gasFormula.eval` definitionally and renders the checked' \
    'syntax tree directly. Here `R` is the decoded round count and `f` is the' \
    'final-block flag. Rows are ordered by their proved schedules summed over' \
    'the public vector suite; this benchmark order is not a claim of global' \
    'dominance for every calldata value.'
  printf '\n'
  printf '| implementation | proved symbolic bound | proof |\n'
  printf '|---|---|---|\n'
  local proved_rows
  proved_rows="$({
    for index in "${!implementation_names[@]}"; do
      report_proved_row "$index"
    done
  } | sort -t $'\t' -k1,1n -k2,2n -k3,3)"
  while IFS=$'\t' read -r _status _rank _name row; do
    printf '%s\n' "$row"
  done <<< "$proved_rows"
  printf '\n<!-- END GENERATED %s GAS REPORT -->\n' "$marker_id"
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
