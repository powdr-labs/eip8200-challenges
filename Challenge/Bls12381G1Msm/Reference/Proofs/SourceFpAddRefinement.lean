import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddCall
import Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

set_option warningAsError true

/-! Arithmetic refinement of the staged G1MSM `fpAdd` result. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics.EVM

private theorem highValue_assoc (ahi alo bhi blo : U256) :
    fpAddHighValue ahi alo bhi blo =
      ahi + bhi + b2w (BitVec.ult (alo + blo) alo) := by
  simp [fpAddHighValue, fpAddLowValue, BitVec.add_assoc]

private theorem fpGeModulusValue_eq_shared (hi lo : U256) :
    fpGeModulusValue hi lo =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
        hi lo := by
  rfl

theorem fpAddResult_eq_shared (ahi alo bhi blo : U256) :
    fpAddResult ahi alo bhi blo =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue
        ahi alo bhi blo := by
  let sLo := alo + blo
  let sHi := ahi + bhi + b2w (BitVec.ult sLo alo)
  have hlo : fpAddLowValue alo blo = sLo := by
    rfl
  have hhi : fpAddHighValue ahi alo bhi blo = sHi := by
    simpa [sHi, sLo] using highValue_assoc ahi alo bhi blo
  have hge :
      fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
          (fpAddLowValue alo blo) =
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
          sHi sLo := by
    rw [fpGeModulusValue_eq_shared, hhi, hlo]
  by_cases hc :
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
        sHi sLo = 0
  · have hlocal : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
        (fpAddLowValue alo blo) = (0#256) := by
      rw [hge]
      exact hc
    unfold fpAddResult fpAddFinalEnv
    rw [if_pos hlocal]
    change (fpAddHighValue ahi alo bhi blo, fpAddLowValue alo blo) = _
    dsimp only [
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue]
    dsimp only [sHi, sLo] at hc
    rw [if_pos hc]
    rw [hhi, hlo]
  · have hlocal : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
        (fpAddLowValue alo blo) ≠ (0#256) := by
      rw [hge]
      exact hc
    unfold fpAddResult fpAddFinalEnv
    rw [if_neg hlocal]
    change (fpAddCorrectHighValue ahi alo bhi blo,
      fpAddCorrectLowValue alo blo) = _
    dsimp only [
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue]
    dsimp only [sHi, sLo] at hc
    rw [if_neg hc]
    simp only [Prod.mk.injEq]
    constructor
    · rw [fpAddCorrectHighValue, hhi, hlo]
    · rw [fpAddCorrectLowValue, hlo]

theorem fpAddResult_toSource (ahi alo bhi blo : U256) :
    ({ hi := YulEvmCompiler.conv (fpAddResult ahi alo bhi blo).1,
       lo := YulEvmCompiler.conv (fpAddResult ahi alo bhi blo).2 } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) =
    Challenge.Bls12381.ProofSupport.Fp.addSource
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } := by
  rw [fpAddResult_eq_shared]
  exact Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpAddValue
    ahi alo bhi blo

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
