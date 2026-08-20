#!/usr/bin/env bash
set -euo pipefail

: "${challenge_dir:?challenge_dir must name the challenge directory}"
: "${challenge_module:?challenge_module must name the Lean namespace}"
: "${challenge_display:?challenge_display must name the challenge}"
: "${scorer_exe:?scorer_exe must name the scorer executable}"

readonly submission_root="$challenge_dir/Submissions"
readonly module_prefix="$challenge_module.Submissions"
readonly allowed_axioms="propext Classical.choice Quot.sound"

trim_whitespace() {
  sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//'
}

check_axiom_output() {
  local theorem_name="$1"
  local raw_output="$2"
  local normalized
  normalized="$(printf '%s' "$raw_output" \
    | sed -E "/^warning: [^:]+: repository '.*' has local changes$/d" \
    | tr '\n' ' ' | tr -s ' ' | trim_whitespace)"

  if [[ "$normalized" == "'$theorem_name' does not depend on any axioms" ]]; then
    return 0
  fi

  local prefix="'$theorem_name' depends on axioms: ["
  if [[ "$normalized" != "$prefix"* ]] || [[ "$normalized" != *"]" ]]; then
    printf 'error: could not parse axiom report for %s\n%s\n' "$theorem_name" "$raw_output" >&2
    return 1
  fi

  local list="${normalized#"$prefix"}"
  list="${list%]}"
  local axiom
  while IFS= read -r axiom; do
    axiom="$(printf '%s' "$axiom" | trim_whitespace)"
    [[ -z "$axiom" ]] && continue
    case " $allowed_axioms " in
      *" $axiom "*) ;;
      *)
        printf 'error: %s depends on forbidden axiom %s\n' "$theorem_name" "$axiom" >&2
        return 1
        ;;
    esac
  done < <(printf '%s\n' "$list" | tr ',' '\n')
}

check_submission() {
  local submission_dir="$1"
  local name
  name="$(basename "$submission_dir")"

  if [[ ! "$name" =~ ^[A-Z][A-Za-z0-9_]*$ ]]; then
    printf 'error: submission directory %s is not an UpperCamelCase Lean identifier\n' "$name" >&2
    return 1
  fi

  local required
  for required in bytecode.hex Bytecode.lean Proof.lean README.md; do
    if [[ ! -f "$submission_dir/$required" ]]; then
      printf 'error: %s is missing %s\n' "$submission_dir" "$required" >&2
      return 1
    fi
  done

  local artifact_hex
  artifact_hex="$(<"$submission_dir/bytecode.hex")"
  if [[ ! "$artifact_hex" =~ ^([0-9a-f][0-9a-f])*$ ]]; then
    printf 'error: %s/bytecode.hex must be canonical lowercase byte pairs without 0x\n' \
      "$submission_dir" >&2
    return 1
  fi

  local module="$module_prefix.$name"
  local theorem_name="$module.correct"
  local build_output
  if ! build_output="$(lake build "$module.Proof" 2>&1)"; then
    printf 'error: submission module failed to build for %s\n%s\n' "$name" "$build_output" >&2
    return 1
  fi

  local check_file
  check_file="$(mktemp "$submission_dir/.submission-check.XXXXXX.lean")"

  {
    printf 'import %s.Proof\n' "$module"
    printf 'import EvmSemantics.Data.Hex\n\n'
    printf 'example : %s.Correct %s.bytecode := %s.correct\n\n' \
      "$challenge_module" "$module" "$module"
    printf '#guard EvmSemantics.Hex.bytesToHex %s.bytecode == ' "$module"
    printf '(include_str "bytecode.hex").trimAscii.copy\n\n'
    printf '#print axioms %s.correct\n' "$module"
  } > "$check_file"

  local lean_output
  if ! lean_output="$(lake env lean "$check_file" 2>&1)"; then
    printf 'error: structural proof check failed for %s\n%s\n' "$name" "$lean_output" >&2
    rm -f -- "$check_file"
    return 1
  fi
  rm -f -- "$check_file"

  if ! check_axiom_output "$theorem_name" "$lean_output"; then
    return 1
  fi

  if ! lake exe "$scorer_exe" --hex="$submission_dir/bytecode.hex"; then
    printf 'error: executable %s checks failed for %s\n' \
      "$challenge_display" "$name" >&2
    return 1
  fi

  printf 'submission %s: proof, artifact, axioms, and scorer accepted\n' "$name"
}

remove_fixture() {
  local fixture_dir="$1"
  rm -f -- "$fixture_dir/bytecode.hex" "$fixture_dir/README.md" \
    "$fixture_dir/Bytecode.lean" "$fixture_dir/Proof.lean"
  rmdir -- "$fixture_dir"
}

run_reference_control() {
  local name="ReferenceSelfTest$$"
  local self_test_dir="$submission_root/$name"
  if [[ -e "$self_test_dir" ]]; then
    printf 'error: refusing to overwrite %s\n' "$self_test_dir" >&2
    return 1
  fi

  mkdir -p -- "$self_test_dir"
  cp "$challenge_dir/Reference/reference.hex" "$self_test_dir/bytecode.hex"
  printf '# known-good checker fixture\n' > "$self_test_dir/README.md"
  {
    printf 'import %s.Reference.Bytecode\n\n' "$challenge_module"
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'def bytecode : ByteArray := %s.referenceBytecode\n\n' "$challenge_module"
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$self_test_dir/Bytecode.lean"
  {
    printf 'import %s.%s.Bytecode\n' "$module_prefix" "$name"
    printf 'import %s.Reference.Proofs.Bytecode.ReferenceCorrect\n\n' \
      "$challenge_module"
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'theorem correct : %s.Correct bytecode := by\n' "$challenge_module"
    printf '  simpa [bytecode] using\n'
    printf '    %s.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct\n\n' \
      "$challenge_module"
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$self_test_dir/Proof.lean"

  local accepted=true
  if ! check_submission "$self_test_dir"; then
    accepted=false
  fi
  remove_fixture "$self_test_dir"

  if [[ "$accepted" == false ]]; then
    printf 'error: submission checker rejected its known-good reference control\n' >&2
    return 1
  fi
  printf 'submission checker positive control: accepted reference proof\n'
}

run_axiom_control() {
  local name="AxiomSelfTest$$"
  local self_test_dir="$submission_root/$name"
  if [[ -e "$self_test_dir" ]]; then
    printf 'error: refusing to overwrite %s\n' "$self_test_dir" >&2
    return 1
  fi

  mkdir -p -- "$self_test_dir"

  printf '00\n' > "$self_test_dir/bytecode.hex"
  printf '# fake checker fixture\n' > "$self_test_dir/README.md"
  {
    printf 'import EvmSemantics.Data.Hex\n\n'
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'def bytecode : ByteArray := EvmSemantics.Hex.hexToBytes "00"\n\n'
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$self_test_dir/Bytecode.lean"
  {
    printf 'import %s.%s.Bytecode\n' "$module_prefix" "$name"
    printf 'import %s.Spec\n\n' "$challenge_module"
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'axiom correct : %s.Correct bytecode\n\n' "$challenge_module"
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$self_test_dir/Proof.lean"

  local accepted=false
  if check_submission "$self_test_dir"; then
    accepted=true
  fi

  remove_fixture "$self_test_dir"

  if [[ "$accepted" == true ]]; then
    printf 'error: submission checker accepted its fake-axiom negative control\n' >&2
    return 1
  fi

  printf 'submission checker negative control: rejected fake axiom as expected\n'
}

run_self_test() {
  run_reference_control
  run_axiom_control
}

main() {
  cd "$(git rev-parse --show-toplevel)"

  if [[ "${1:-}" == "--self-test" ]]; then
    run_self_test
    return
  fi
  if [[ $# -ne 0 ]]; then
    printf 'usage: %s [--self-test]\n' "$0" >&2
    return 2
  fi

  local found=false
  local submission_dir
  for submission_dir in "$submission_root"/*; do
    [[ -d "$submission_dir" ]] || continue
    found=true
    check_submission "$submission_dir"
  done

  if [[ "$found" == false ]]; then
    printf 'no %s candidate directories found\n' "$challenge_display"
  fi
}
