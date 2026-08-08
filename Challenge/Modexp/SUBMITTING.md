# Submitting MODEXP bytecode

## Required result

For concrete EVM `bytecode`, prove:

```lean
Challenge.Modexp.Correct bytecode
```

`Correct` is defined in [`Spec.lean`](Spec.lean). It covers every Osaka-valid
EIP-198 tuple, including missing operand bytes interpreted as trailing zeroes.

## Directory and names

Choose an UpperCamelCase name such as `FastModexp` and add:

```text
Challenge/Modexp/Submissions/FastModexp/
  bytecode.hex
  Bytecode.lean
  Proof.lean
  Gas.lean       # optional proved gas schedule
  README.md
```

Use namespace `Challenge.Modexp.Submissions.FastModexp`. `bytecode.hex` must
contain canonical lowercase byte pairs without a `0x` prefix.

`Bytecode.lean` must expose `bytecode : ByteArray`, and `Proof.lean` must
expose:

```lean
theorem correct : Challenge.Modexp.Correct bytecode := by
  -- proof
```

CI checks the theorem's exact type, its transitive axiom footprint, the Lean
byte array against `bytecode.hex`, and the artifact against every executable
MODEXP vector.

## Optional proved gas formula

MODEXP gas cannot in general be a function of `CALLDATASIZE` alone: the three
header lengths and operand values affect execution. To enter the proved-gas
leaderboard, add `Gas.lean` with:

```lean
import Challenge.Modexp.Submissions.FastModexp.Proof
import Challenge.Modexp.AdditionalGoals.GasSchedule

namespace Challenge.Modexp.Submissions.FastModexp

def gasFormula : Challenge.Modexp.GasFormula :=
  -- symbolic bound over the complete calldata value

def gasSchedule : ByteArray → Nat := gasFormula.eval

theorem gasSchedule_correct :
    Challenge.Modexp.CorrectWithSchedule bytecode gasSchedule := by
  -- proof

end Challenge.Modexp.Submissions.FastModexp
```

The formula language exposes calldata size, the decoded base/exponent/modulus
lengths (`B`, `E`, `M`), the padded modulus value (`V_M`), arithmetic, natural
division, EVM memory cost, and explicit zero/upper-bound conditionals. The
checker requires `gasSchedule = gasFormula.eval` by definitional equality,
renders the syntax tree directly as LaTeX, and rejects forbidden axioms.

Proved entries are ordered by the sum of their schedules over the public
Tier-1 vector suite. This is a reproducible benchmark rank, not a claim that
the formulas are globally ordered over every valid MODEXP tuple.

## Local checks

```sh
lake build
lake exe modexpchallenge --hex=Challenge/Modexp/Submissions/FastModexp/bytecode.hex
scripts/check-modexp-submissions.sh
scripts/check-modexp-gas-report.sh
```

The shared direct-bytecode proof toolkit is under [`../EvmProof/`](../EvmProof/),
and the bundled proof is a complete worked example. Measured gas and vector
passes are useful falsification evidence; only the Lean theorems establish the
universal claims.

## PR guidance

Candidate PRs are mechanically confined to one candidate directory. The only
permitted change outside it is the generated gas-report section in this
challenge's [`README.md`](README.md). Changes to `Spec.lean`, the central
checker, proof support, pinned dependencies, CI, or any other path alter the
trust boundary and must be proposed as a separate infrastructure PR. The
boundary policy runs from the trusted base branch, so changing the policy in a
candidate PR cannot bypass it.
