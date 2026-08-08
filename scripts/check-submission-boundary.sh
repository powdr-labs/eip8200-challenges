#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

usage() {
  printf 'usage: %s BASE_COMMIT HEAD_COMMIT\n       %s --self-test\n' "$0" "$0" >&2
}

policy_error() {
  printf 'submission-boundary error: %s\n' "$1" >&2
}

gas_marker() {
  [[ "$1" =~ ^[A-Z][A-Za-z0-9_]*$ ]] || return 1
  printf '%s' "$1" | tr '[:lower:]' '[:upper:]'
}

render_outside_gas_report() {
  local revision="$1"
  local path="$2"
  local marker="$3"
  local begin="<!-- BEGIN GENERATED $marker GAS REPORT -->"
  local end="<!-- END GENERATED $marker GAS REPORT -->"

  git show "$revision:$path" | awk -v begin="$begin" -v end="$end" '
    $0 == begin {
      if (inside || saw_begin) exit 2
      inside = 1
      saw_begin = 1
      print
      next
    }
    $0 == end {
      if (!inside || saw_end) exit 3
      inside = 0
      saw_end = 1
      print
      next
    }
    !inside { print }
    END {
      if (!saw_begin || !saw_end || inside) exit 4
    }
  '
}

check_regular_file() {
  local revision="$1"
  local path="$2"
  local entry mode
  entry="$(git ls-tree "$revision" -- "$path")"
  if [[ -z "$entry" ]]; then
    policy_error "$path is missing from the candidate head"
    return 1
  fi
  mode="${entry%% *}"
  if [[ "$mode" != "100644" ]]; then
    policy_error "$path must be a regular non-executable file (found mode $mode)"
    return 1
  fi
}

check_known_challenge() {
  local revision="$1"
  local challenge="$2"
  local path="Challenge/$challenge/Submissions/README.md"
  local entry mode
  entry="$(git ls-tree "$revision" -- "$path")"
  mode="${entry%% *}"
  if [[ -z "$entry" || "$mode" != "100644" ]]; then
    policy_error "$challenge is not an established submission challenge in the trusted base"
    return 1
  fi
}

check_readme_change() {
  local base="$1"
  local head="$2"
  local challenge="$3"
  local path="Challenge/$challenge/README.md"
  local marker tmp_dir
  marker="$(gas_marker "$challenge")"
  tmp_dir="$(mktemp -d)"

  if ! render_outside_gas_report "$base" "$path" "$marker" > "$tmp_dir/base"; then
    rm -rf -- "$tmp_dir"
    policy_error "$path has malformed generated gas-report markers in the base"
    return 1
  fi
  if ! render_outside_gas_report "$head" "$path" "$marker" > "$tmp_dir/head"; then
    rm -rf -- "$tmp_dir"
    policy_error "$path has malformed generated gas-report markers in the candidate head"
    return 1
  fi
  if ! cmp -s "$tmp_dir/base" "$tmp_dir/head"; then
    rm -rf -- "$tmp_dir"
    policy_error "$path changed outside its generated gas-report section"
    return 1
  fi
  rm -rf -- "$tmp_dir"
}

check_boundary() {
  local base="$1"
  local head="$2"
  local merge_base

  if ! git cat-file -e "$base^{commit}" 2>/dev/null; then
    policy_error "base revision $base is not a commit"
    return 1
  fi
  if ! git cat-file -e "$head^{commit}" 2>/dev/null; then
    policy_error "head revision $head is not a commit"
    return 1
  fi
  if ! merge_base="$(git merge-base "$base" "$head")"; then
    policy_error "base and head do not share history"
    return 1
  fi

  local -a statuses=()
  local -a paths=()
  local status path
  while IFS= read -r -d '' status && IFS= read -r -d '' path; do
    statuses+=("$status")
    paths+=("$path")
  done < <(git diff --name-status -z --no-renames "$merge_base" "$head")

  local candidate_root=""
  local candidate_challenge=""
  local candidate_name=""
  local index
  for index in "${!paths[@]}"; do
    path="${paths[$index]}"
    if [[ "$path" =~ ^Challenge/([^/]+)/Submissions/([^/]+)(/.*)?$ ]]; then
      local found_challenge="${BASH_REMATCH[1]}"
      local found_name="${BASH_REMATCH[2]}"
      # The directory index is infrastructure, not a candidate directory.
      if [[ "$found_name" == "README.md" && -z "${BASH_REMATCH[3]-}" ]]; then
        continue
      fi
      local found_root="Challenge/$found_challenge/Submissions/$found_name"
      if [[ -n "$candidate_root" && "$candidate_root" != "$found_root" ]]; then
        policy_error "candidate work spans both $candidate_root and $found_root"
        return 1
      fi
      candidate_root="$found_root"
      candidate_challenge="$found_challenge"
      candidate_name="$found_name"
    fi
  done

  if [[ -z "$candidate_root" ]]; then
    printf 'submission boundary: no candidate-directory changes; infrastructure PR accepted\n'
    return 0
  fi
  if [[ ! "$candidate_name" =~ ^[A-Z][A-Za-z0-9_]*$ ]]; then
    policy_error "$candidate_name is not an UpperCamelCase Lean identifier"
    return 1
  fi
  if ! check_known_challenge "$merge_base" "$candidate_challenge"; then
    return 1
  fi

  local report_path="Challenge/$candidate_challenge/README.md"
  local report_changed=false
  for index in "${!paths[@]}"; do
    status="${statuses[$index]}"
    path="${paths[$index]}"
    if [[ "$path" == "$candidate_root" || "$path" == "$candidate_root/"* ]]; then
      case "$status" in
        A|M)
          if ! check_regular_file "$head" "$path"; then return 1; fi
          ;;
        D) ;;
        *)
          policy_error "$path has unsupported Git status $status"
          return 1
          ;;
      esac
    elif [[ "$path" == "$report_path" ]]; then
      if [[ "$status" != "M" ]]; then
        policy_error "$report_path may only be modified, not added or deleted"
        return 1
      fi
      report_changed=true
    else
      policy_error "candidate PR also changes protected path $path"
      return 1
    fi
  done

  local required
  for required in bytecode.hex Bytecode.lean Proof.lean README.md; do
    if ! check_regular_file "$head" "$candidate_root/$required"; then return 1; fi
  done
  if [[ "$report_changed" == true ]]; then
    if ! check_readme_change "$merge_base" "$head" "$candidate_challenge"; then
      return 1
    fi
  fi

  printf 'submission boundary: %s is isolated to its candidate files' "$candidate_root"
  if [[ "$report_changed" == true ]]; then
    printf ' and generated gas report'
  fi
  printf '\n'
}

write_candidate() {
  local root="$1"
  mkdir -p -- "$root"
  printf '00\n' > "$root/bytecode.hex"
  printf 'def bytecode := ByteArray.empty\n' > "$root/Bytecode.lean"
  printf 'theorem correct : True := by trivial\n' > "$root/Proof.lean"
  printf '# fixture\n' > "$root/README.md"
}

write_challenge_readme() {
  local challenge="$1"
  local marker
  marker="$(gas_marker "$challenge")"
  mkdir -p -- "Challenge/$challenge/Submissions"
  printf '# candidate index\n' > "Challenge/$challenge/Submissions/README.md"
  {
    printf '# %s\n\n' "$challenge"
    printf '<!-- BEGIN GENERATED %s GAS REPORT -->\n' "$marker"
    printf 'base row\n'
    printf '<!-- END GENERATED %s GAS REPORT -->\n\n' "$marker"
    printf 'trusted prose\n'
  } > "Challenge/$challenge/README.md"
}

commit_fixture() {
  local message="$1"
  git add -A
  git commit -qm "$message"
  git rev-parse HEAD
}

expect_accept() {
  local label="$1"
  local base="$2"
  local head="$3"
  if ! check_boundary "$base" "$head" >/dev/null; then
    printf 'self-test error: expected acceptance for %s\n' "$label" >&2
    return 1
  fi
}

expect_reject() {
  local label="$1"
  local base="$2"
  local head="$3"
  if check_boundary "$base" "$head" >/dev/null 2>&1; then
    printf 'self-test error: expected rejection for %s\n' "$label" >&2
    return 1
  fi
}

run_self_test() {
  local old_pwd="$PWD"
  local tmp_dir repo base head
  tmp_dir="$(mktemp -d)"
  repo="$tmp_dir/repo"
  trap 'cd "$old_pwd"; rm -rf -- "$tmp_dir"' RETURN

  git init -q "$repo"
  cd "$repo"
  git config user.name 'Submission Policy Test'
  git config user.email 'submission-policy@example.invalid'
  write_challenge_readme Sha256
  write_challenge_readme Ripemd160
  write_challenge_readme Modexp
  write_challenge_readme Blake2f
  write_candidate 'Challenge/Sha256/Submissions/Existing'
  mkdir -p scripts Challenge/Ripemd160 Challenge/Blake2f
  printf '# trusted checker\n' > scripts/checker.sh
  printf 'import EvmSemantics.EVM.BigStep\n' > Challenge/Ripemd160/Spec.lean
  printf 'import EvmSemantics.EVM.BigStep\n' > Challenge/Blake2f/Spec.lean
  base="$(commit_fixture base)"

  write_candidate 'Challenge/Ripemd160/Submissions/FastRipemd'
  sed -i 's/base row/candidate row/' Challenge/Ripemd160/README.md
  head="$(commit_fixture valid-new-candidate)"
  expect_accept 'new candidate plus generated report' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Blake2f/Submissions/FutureChallenge'
  sed -i 's/base row/candidate row/' Challenge/Blake2f/README.md
  head="$(commit_fixture blake2f-candidate)"
  expect_accept 'BLAKE2f candidate plus generated report' "$base" "$head"

  git reset --hard -q "$base"
  printf '\n-- stronger proof\n' >> Challenge/Sha256/Submissions/Existing/Proof.lean
  head="$(commit_fixture valid-existing-candidate-update)"
  expect_accept 'existing candidate proof update' "$base" "$head"

  git reset --hard -q "$base"
  printf '# infrastructure documentation\n' >> Challenge/Ripemd160/Spec.lean
  head="$(commit_fixture infrastructure-only)"
  expect_accept 'infrastructure-only PR' "$base" "$head"

  git reset --hard -q "$base"
  printf '\nindex documentation\n' >> Challenge/Sha256/Submissions/README.md
  head="$(commit_fixture submission-index-only)"
  expect_accept 'submission index infrastructure change' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Ripemd160/Submissions/MixedSpec'
  printf '\ndef Correct := True\n' >> Challenge/Ripemd160/Spec.lean
  head="$(commit_fixture mixed-spec)"
  expect_reject 'candidate mixed with spec change' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Blake2f/Submissions/MixedSpec'
  printf '\ndef Correct := True\n' >> Challenge/Blake2f/Spec.lean
  head="$(commit_fixture blake2f-mixed-spec)"
  expect_reject 'BLAKE2f candidate mixed with spec change' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Sha256/Submissions/TwoChallenges'
  write_candidate 'Challenge/Modexp/Submissions/TwoChallenges'
  head="$(commit_fixture cross-challenge)"
  expect_reject 'two challenge candidates' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Ripemd160/Submissions/ReadmeEscape'
  printf '\nuntrusted prose\n' >> Challenge/Ripemd160/README.md
  head="$(commit_fixture readme-escape)"
  expect_reject 'README change outside generated report' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Modexp/Submissions/CheckerChange'
  printf '# bypass\n' >> scripts/checker.sh
  head="$(commit_fixture checker-change)"
  expect_reject 'candidate mixed with checker change' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Invented/Submissions/Unchecked'
  head="$(commit_fixture invented-challenge)"
  expect_reject 'candidate for a challenge absent from the trusted base' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Ripemd160/Submissions/Symlinked'
  rm Challenge/Ripemd160/Submissions/Symlinked/README.md
  ln -s ../../README.md Challenge/Ripemd160/Submissions/Symlinked/README.md
  head="$(commit_fixture symlink)"
  expect_reject 'symlinked candidate file' "$base" "$head"

  git reset --hard -q "$base"
  mkdir -p Challenge/Modexp/Submissions
  ln -s ../README.md Challenge/Modexp/Submissions/RootLink
  head="$(commit_fixture root-symlink)"
  expect_reject 'candidate root represented by a symlink' "$base" "$head"

  git reset --hard -q "$base"
  mkdir -p Challenge/Sha256/Submissions/Incomplete
  printf 'theorem correct : True := by trivial\n' > \
    Challenge/Sha256/Submissions/Incomplete/Proof.lean
  head="$(commit_fixture incomplete)"
  expect_reject 'missing required candidate files' "$base" "$head"

  git reset --hard -q "$base"
  write_candidate 'Challenge/Ripemd160/Submissions/lowercase'
  head="$(commit_fixture invalid-name)"
  expect_reject 'invalid candidate name' "$base" "$head"

  git reset --hard -q "$base"
  rm -rf Challenge/Sha256/Submissions/Existing
  head="$(commit_fixture deletion)"
  expect_reject 'candidate deletion' "$base" "$head"

  printf 'submission-boundary self-test: all controls passed\n'
}

if [[ "${1:-}" == "--self-test" && $# -eq 1 ]]; then
  run_self_test
elif [[ $# -eq 2 ]]; then
  check_boundary "$1" "$2"
else
  usage
  exit 2
fi
