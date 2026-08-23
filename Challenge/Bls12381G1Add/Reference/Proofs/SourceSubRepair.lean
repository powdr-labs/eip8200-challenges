import Challenge.Bls12381G1Add.Reference.Proofs.SourceSubRaw

set_option warningAsError true

/-! # Word conversion for the frozen G1ADD field-subtraction repair -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem conv_fpSubRepairValue (diff : U256 × U256) :
    convPair (fpSubRepairValue diff) =
      Challenge.Bls12381.ProofSupport.Fp.subRepair (convPair diff) := by
  have hhi : YulEvmCompiler.conv (BitVec.ofNat 256
      34565483545414906068789196026815425751) =
      Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  have hlo : YulEvmCompiler.conv (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167851) =
      Challenge.Bls12381.ProofSupport.Fp.modulusLo := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  unfold convPair fpSubRepairValue
    Challenge.Bls12381.ProofSupport.Fp.subRepair
  repeat rw [YulEvmCompiler.conv_add]
  repeat rw [YulEvmCompiler.conv_lt]
  rw [hhi, hlo]
  rw [YulEvmCompiler.conv_add, hlo]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
