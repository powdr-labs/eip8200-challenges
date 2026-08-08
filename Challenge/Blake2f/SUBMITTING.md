# Submitting BLAKE2f bytecode

For `bytecode : ByteArray`, prove `Challenge.Blake2f.Correct bytecode`.
Correctness covers every realizable calldata: exact 64-byte output for valid
213-byte EIP-152 input and exceptional failure otherwise. Address `0x09` is
disabled in the specified frame.

Create an UpperCamelCase directory containing:

```text
Challenge/Blake2f/Submissions/FastBlake2f/
  bytecode.hex
  Bytecode.lean
  Proof.lean
  Gas.lean       # optional
  README.md
```

Hex is canonical lowercase byte pairs without `0x`. `Bytecode.lean` exposes
`bytecode`; `Proof.lean` exposes exactly:

```lean
theorem correct : Challenge.Blake2f.Correct bytecode := by
  -- proof
```

The stable direct target is
`Challenge.Blake2f.ProofSupport.Bytecode.DirectProof bytecode`. The verified
source alternative is `ProofSupport.Yul.ComputesBehavior`, including malformed
input `invalid()` behavior.

Optional gas proofs define a `GasFormula`, its evaluator schedule, and prove
`CorrectWithSchedule bytecode gasSchedule`. Formulas may use calldata size,
round count, final flag, validity, constants, addition, and multiplication.
Universal proofs may use only Lean's standard logical axioms; measurements and
fixed-artifact `native_decide` checks are not correctness proofs.

Use these exact declarations in `Gas.lean` so the generated leaderboard can
check and render the proved schedule:

```lean
def gasFormula : Challenge.Blake2f.GasFormula := by
  -- symbolic expression

def gasSchedule : ByteArray → Nat := gasFormula.eval

theorem gasSchedule_correct :
    Challenge.Blake2f.CorrectWithSchedule bytecode gasSchedule := by
  -- proof
```

Run the same checks as CI with:

```sh
scripts/check-blake2f-submissions.sh
scripts/report-blake2f-gas.sh
scripts/check-blake2f-gas-report.sh
```

## PR guidance

Candidate PRs are mechanically confined to one candidate directory. The only
permitted change outside it is the generated gas-report section in this
challenge's [`README.md`](README.md). Changes to `Spec.lean`, the central
checker, proof support, pinned dependencies, CI, or any other path alter the
trust boundary and must be proposed as a separate infrastructure PR. The
boundary policy runs from the trusted base branch, so changing the policy in a
candidate PR cannot bypass it.
