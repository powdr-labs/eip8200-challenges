import Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

set_option warningAsError true

/-! # Word conversion for the frozen G1ADD field-subtraction prefix -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics.EVM

/-- Convert a source high/low word pair into the shared BLS limb carrier. -/
def convPair (words : U256 × U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv words.1, lo := YulEvmCompiler.conv words.2 }

theorem conv_fpSubRawValue (ahi alo bhi blo : U256) :
    convPair (fpSubRawValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.subRaw
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } := by
  simp [convPair, fpSubRawValue,
    Challenge.Bls12381.ProofSupport.Fp.subRaw,
    YulEvmCompiler.conv_sub, YulEvmCompiler.conv_gt]

theorem conv_fpSubNeedsRepairValue (diff : U256 × U256) :
    YulEvmCompiler.conv (fpSubNeedsRepairValue diff) =
      UInt256.gt (convPair diff).hi
        Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
  have hhi : YulEvmCompiler.conv (BitVec.ofNat 256
      34565483545414906068789196026815425751) =
      Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  unfold fpSubNeedsRepairValue convPair
  rw [YulEvmCompiler.conv_gt, hhi]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
