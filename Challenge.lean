import Challenge.EvmProof
import Challenge.Blake2f
import Challenge.Modexp
import Challenge.Ripemd160
import Challenge.Sha256
set_option warningAsError true
/-!
# EIP-8200 challenges

Verified replacements for Ethereum precompiles: EVM bytecode, plus a
machine-checked proof that the bytecode computes what the precompile
computed.

SHA-256 (`0x02`), RIPEMD-160 (`0x03`), MODEXP (`0x05`), and BLAKE2f (`0x09`)
are the first
challenges:

* `Challenge.EvmProof` — verified disassembly and direct small-step proof
  combinators for raw-bytecode submissions.
* `Challenge.Sha256.Spec` — the minimal auditor-facing `Correct` predicate and
  fixed initial EVM state it quantifies over.
* `Challenge.Sha256.ProofSupport` — reusable Yul and direct-bytecode reductions
  and initial-state lemmas for proving `Correct`.
* `Challenge.Sha256.Reference` — the bundled Yul and frozen 1,524-byte artifact.
* `Challenge.Sha256.Reference.Proofs` — implementation-specific correctness
  proofs, including the complete direct EVM proof of the frozen bytes.
* `Challenge.Sha256.Scorer` — Tier 1, falsification by execution
  (`lake exe sha256challenge`).
* `Challenge.Modexp.Spec` — the successful Osaka/EIP-7823 MODEXP interface.
* `Challenge.Modexp.Reference` — reference Yul and its frozen 1,284-byte artifact.
* `Challenge.Modexp.Reference.Proofs` — complete correctness and exact-gas
  proofs for the frozen MODEXP bytecode.
* `Challenge.Modexp.Scorer` — EIP-198 and arbitrary-precision falsification
  (`lake exe modexpchallenge`).
* `Challenge.Ripemd160.Spec` — the minimal RIPEMD-160 precompile-equivalence
  statement.
* `Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect` — the
  unconditional direct-bytecode correctness and exact-gas theorems.
* `Challenge.Ripemd160.Scorer` — executable clean- and dirty-memory vectors
  (`lake exe ripemd160challenge`).
* `Challenge.Blake2f.Spec` — the complete successful and malformed EIP-152
  interface with the incumbent `0x09` precompile disabled.
* `Challenge.Blake2f.Scorer` — executable EIP-152 and malformed-input vectors
  (`lake exe blake2fchallenge`).

See each challenge directory for its specification, audit map, submission
instructions, reference artifact, and proof.
-/
