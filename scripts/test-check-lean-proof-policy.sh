#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scanner="$repo_root/scripts/check-lean-proof-policy.py"
fixture_dir="$(mktemp -d)"
trap 'rm -rf "$fixture_dir"' EXIT

expect_rejected() {
  local name="$1"
  local expected="$2"
  local source="$3"
  local fixture="$fixture_dir/$name.lean"
  local stderr_file="$fixture_dir/$name.stderr"
  mkdir -p -- "$(dirname "$fixture")"
  printf '%s\n' "$source" > "$fixture"
  if python3 "$scanner" "$fixture" 2> "$stderr_file"; then
    printf 'expected scanner to reject %s\n' "$name" >&2
    exit 1
  fi
  grep -Fq "$expected" "$stderr_file"
}

# Raw substring policy: source context and Lean token boundaries are irrelevant.
expect_rejected escaped_identifier 'forbidden raw spelling: sorry' \
  'def escaped := «sorry»'
expect_rejected line_comment 'forbidden raw spelling: sorry' \
  '-- sorry must be rejected even in prose'
expect_rejected nested_comment 'forbidden raw spelling: admit' \
  '/- outer /- admit -/ comment -/'
expect_rejected ordinary_string 'forbidden raw spelling: native_decide' \
  'def text := "native_decide"'
expect_rejected raw_string 'forbidden raw spelling: CertifiedArtifact' \
  'def text := r###"CertifiedArtifact with embedded \" quote"###'
expect_rejected char_literal 'forbidden raw spelling: sorry' \
  "#check ('{' : Char); #check sorry"
expect_rejected string_interpolation 'forbidden raw spelling: sorry' \
  'def escapedProof : String := s!"{(by sorry : Nat)}"'
expect_rejected interpolated_char_brace 'forbidden raw spelling: sorry' \
  '#check s!"{('\''{'\'' : Char)}{(by sorry : Nat)}"'
expect_rejected message_interpolation 'forbidden raw spelling: sorry' \
  '#check m!"{(by sorry : Nat)}"'
expect_rejected format_interpolation 'forbidden raw spelling: sorry' \
  '#check f!"{(by sorry : Nat)}"'
expect_rejected plain_string_braces 'forbidden raw spelling: sorry' \
  'def text := "{sorry}"'
expect_rejected unicode_operator_adjacency 'forbidden raw spelling: sorry' \
  '#check 1 ⊕sorry'
expect_rejected ascii_operator_adjacency 'forbidden raw spelling: sorry' \
  '#check 1+sorry'
expect_rejected identifier_suffix 'forbidden raw spelling: sorry' \
  '#check sorry?'
expect_rejected raw_prefix_adjacency 'forbidden raw spelling: sorry' \
  '#check r#"safe"#sorry'
expect_rejected sorry_ax_substring 'forbidden raw spelling: sorryAx' \
  '#check prefixsorryAxSuffix'

expect_rejected 'Challenge/Bls12381G1Add/BroadImport' \
  'forbidden broad BLS proof-support import' \
  'import Challenge.Bls12381.ProofSupport'
expect_rejected 'Challenge/Bls12381G2Add/BroadImport' \
  'forbidden broad BLS proof-support import' \
  'import Challenge.Bls12381.ProofSupport'
expect_rejected 'Checks/Bls12381G1AddCheckImport' \
  'forbidden completed-ADD check-to-check import' \
  'import Checks.Bls12381G1AddFinalCorrectness'
expect_rejected 'Checks/Bls12381G2AddCheckImport' \
  'forbidden completed-ADD check-to-check import' \
  'import Checks.Bls12381G2AddReference'

expect_rejected private_axiom 'forbidden axiom declaration' \
  'private axiom hiddenEscape : True'
expect_rejected multiline_axiom 'forbidden axiom declaration' $'private\naxiom hiddenEscape : True'
expect_rejected comment_axiom 'forbidden axiom declaration' \
  '-- private axiom hiddenEscape : True'
expect_rejected escaped_axiom 'forbidden axiom declaration' \
  '#check «axiom»'
expect_rejected operator_axiom 'forbidden axiom declaration' \
  '#check 1+axiom'
expect_rejected string_axiom 'forbidden axiom declaration' \
  'def text := "axiom"'
expect_rejected commented_heartbeat 'unparseable maxHeartbeats' \
  'set_option maxHeartbeats /- parser gap -/ 0 in example : True := by trivial'

for literal in 0 00 0_0 0x0 0X00 0x0_0 0b0 0B00 0b0_0 0o0 0O00 0o0_0; do
  expect_rejected "zero-${literal}" 'unlimited maxHeartbeats' \
    "set_option maxHeartbeats ${literal} in example : True := by trivial"
done

cat > "$fixture_dir/accepted.lean" <<'EOF'
#print axioms existingTheorem
set_option maxHeartbeats 1000000 in
example : True := by trivial
EOF
python3 "$scanner" "$fixture_dir/accepted.lean"

mkdir -p "$fixture_dir/Challenge/Bls12381G1Add"
cat > "$fixture_dir/Challenge/Bls12381G1Add/NarrowImport.lean" <<'EOF'
import Challenge.Bls12381.ProofSupport.FpAddSub
EOF
python3 "$scanner" "$fixture_dir/Challenge/Bls12381G1Add/NarrowImport.lean"

mkdir -p "$fixture_dir/Checks"
cat > "$fixture_dir/Checks/Bls12381G2AddProductionImport.lean" <<'EOF'
import Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness
EOF
python3 "$scanner" "$fixture_dir/Checks/Bls12381G2AddProductionImport.lean"

for literal in 1 01 1_0 0x1 0X10 0x1_0 0b1 0B10 0b1_0 0o1 0O10 0o1_0; do
  printf 'set_option maxHeartbeats %s in\nexample : True := by trivial\n' \
    "$literal" > "$fixture_dir/nonzero-${literal}.lean"
  python3 "$scanner" "$fixture_dir/nonzero-${literal}.lean"
done

printf 'Conservative Lean proof-policy scanner self-test: PASS\n'
