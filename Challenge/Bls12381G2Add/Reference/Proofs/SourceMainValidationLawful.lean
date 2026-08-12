import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainValidationExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointPredicatesRefinement

set_option warningAsError true

/-! # Lawful meaning of the G2ADD main validation word

This module deliberately stops at canonical source-memory coordinates.  The
calldata/codec bridge lives in a later module, so checking this Boolean
conjunction never unfolds the sixteen-word decoder.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainAfterPoint2Valid_memory (yst : EvmState) :
    (mainAfterPoint2Valid yst).memory = (mainDecodedState yst).memory := by
  rfl

theorem mainAfterValidationReads_memory (yst : EvmState) :
    (mainAfterValidationReads yst).memory = (mainDecodedState yst).memory := by
  rfl

/-- The source `and` passes exactly when both point-validation calls return
one. -/
theorem mainValidationValue_ne_zero_iff (yst : EvmState) :
    mainValidationValue yst ≠ 0 ↔
      mainPoint1Valid yst = 1 ∧ mainPoint2Valid yst = 1 := by
  have h1 : mainPoint1Valid yst = 0 ∨ mainPoint1Valid yst = 1 := by
    unfold mainPoint1Valid
    exact pointValidValue_zero_or_one (mainAfterPoint2Valid yst) 0
  have h2 : mainPoint2Valid yst = 0 ∨ mainPoint2Valid yst = 1 := by
    unfold mainPoint2Valid
    exact pointValidValue_zero_or_one (mainDecodedState yst) 256
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    unfold mainValidationValue <;> rw [h1, h2] <;> decide

/-- Passing main validation gives canonical Fp2 coordinates and zero EIP
padding for both points, all stated over the decoded-memory boundary. -/
theorem mainValidation_canonical (yst : EvmState)
    (hvalid : mainValidationValue yst ≠ 0) :
    (Fp2.Canonical (fp2At (mainDecodedState yst) 0) ∧
      Fp2.Canonical (fp2At (mainDecodedState yst) 128) ∧
      PointPaddingZero (mainDecodedState yst) 0) ∧
    (Fp2.Canonical (fp2At (mainDecodedState yst) 256) ∧
      Fp2.Canonical (fp2At (mainDecodedState yst) 384) ∧
      PointPaddingZero (mainDecodedState yst) 256) := by
  obtain ⟨h1, h2⟩ := (mainValidationValue_ne_zero_iff yst).mp hvalid
  have hp1 := (pointValidValue_eq_one_iff (mainAfterPoint2Valid yst) 0).mp h1
  have hp2 := (pointValidValue_eq_one_iff (mainDecodedState yst) 256).mp h2
  have hfp0 : fp2At (mainAfterPoint2Valid yst) 0 =
      fp2At (mainDecodedState yst) 0 := by
    simp only [fp2At]
    rw [mainAfterPoint2Valid_memory]
  have hfp128 : fp2At (mainAfterPoint2Valid yst) 128 =
      fp2At (mainDecodedState yst) 128 := by
    simp only [fp2At]
    rw [mainAfterPoint2Valid_memory]
  have hpad : PointPaddingZero (mainAfterPoint2Valid yst) 0 ↔
      PointPaddingZero (mainDecodedState yst) 0 := by
    unfold PointPaddingZero
    rw [mainAfterPoint2Valid_memory]
  rw [show (0 : U256) + BitVec.ofNat 256 128 = 128 by decide,
    hfp0, hfp128, hpad] at hp1
  rw [show (256 : U256) + BitVec.ofNat 256 128 = 384 by decide] at hp2
  exact ⟨hp1, hp2⟩

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
