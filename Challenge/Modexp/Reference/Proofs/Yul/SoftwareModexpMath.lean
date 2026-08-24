import Challenge.Modexp.Reference.Proofs.Yul.Execution
import Challenge.YulProof.SoftwareModexpMath

set_option warningAsError true

/-!
# Existing MODEXP source as an instance of the shared arithmetic contract

The general MODEXP source has a calldata/halting ABI, whereas BLS field
inversion uses a normally returning local function.  This adapter therefore
shares the mathematical result property without pretending the two execution
ABIs are interchangeable.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.SoftwareModexpMath

open EvmSemantics.EVM

/-- Mathematical operation decoded from one EIP-198 input tuple. -/
def operationOfInput (input : ByteArray) :
    Challenge.YulProof.SoftwareModexpMath.Operation :=
  let bsize := Challenge.Modexp.baseSize input
  let esize := Challenge.Modexp.exponentSize input
  let msize := Challenge.Modexp.modulusSize input
  { base := Precompile.bytesToNatPadded input 96 bsize
    exponent := Precompile.bytesToNatPadded input (96 + bsize) esize
    modulus := Precompile.bytesToNatPadded input (96 + bsize + esize) msize
    outputSize := msize }

/-- The auditor-facing MODEXP byte specification is exactly the fixed-width
encoding of the shared mathematical operation. -/
theorem spec_resultBytes (input : ByteArray) :
    Challenge.YulProof.SoftwareModexpMath.ResultBytes
      (operationOfInput input) (Challenge.Modexp.spec input).toList := by
  unfold Challenge.YulProof.SoftwareModexpMath.ResultBytes
    Challenge.YulProof.SoftwareModexpMath.Operation.resultNat
  by_cases hzero : Challenge.Modexp.modulusSize input = 0
  · rw [Challenge.Modexp.spec, if_pos hzero]
    simp [operationOfInput, hzero, Precompile.natToBytes,
      EvmSemantics.Data.Bytes.natToBytesPadded]
  · rw [Challenge.Modexp.spec, if_neg hzero]
    rfl

/-- Source-level correctness paired with the shared mathematical result
property.  The first conjunct is the existing relational-Yul theorem; the
second is the stable adapter that remains valid if the implementation changes
while continuing to prove the same public specification. -/
def MathCorrect (program : YulSemantics.Block YulSemantics.EVM.Op) : Prop :=
  Challenge.Modexp.Yul.Correct program ∧
    ∀ input : ByteArray,
      Challenge.YulProof.SoftwareModexpMath.ResultBytes
        (operationOfInput input) (Challenge.Modexp.spec input).toList

theorem verifiedProgram_mathCorrect :
    MathCorrect Challenge.Modexp.Reference.Proofs.Yul.verifiedProgram :=
  ⟨Challenge.Modexp.Reference.Proofs.Yul.Execution.verifiedProgram_computesResult,
    spec_resultBytes⟩

end Challenge.Modexp.Reference.Proofs.Yul.SoftwareModexpMath
