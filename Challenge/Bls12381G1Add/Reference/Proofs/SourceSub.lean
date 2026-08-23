import Challenge.Bls12381G1Add.Reference.Proofs.SourceSubRepair

set_option warningAsError true

/-! # Frozen G1ADD field-subtraction refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics.EVM

/-- The frozen source subtraction helper refines to the approved source-faithful
BLS limb schedule. -/
theorem conv_fpSubValue (ahi alo bhi blo : U256) :
    convPair (fpSubValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.subSource
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } := by
  let diff := fpSubRawValue ahi alo bhi blo
  let a : Challenge.Bls12381.ProofSupport.Fp.Limbs :=
    { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
  let b : Challenge.Bls12381.ProofSupport.Fp.Limbs :=
    { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }
  change convPair (fpSubValue ahi alo bhi blo) =
    Challenge.Bls12381.ProofSupport.Fp.subSource a b
  have hraw : convPair diff =
      Challenge.Bls12381.ProofSupport.Fp.subRaw a b := by
    exact conv_fpSubRawValue ahi alo bhi blo
  have hrepair : YulEvmCompiler.conv (fpSubNeedsRepairValue diff) =
      UInt256.gt (Challenge.Bls12381.ProofSupport.Fp.subRaw a b).hi
        Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
    rw [conv_fpSubNeedsRepairValue, hraw]
  by_cases hc : fpSubNeedsRepairValue diff = 0
  · have hkeep : ¬(UInt256.gt
        (Challenge.Bls12381.ProofSupport.Fp.subRaw a b).hi
          Challenge.Bls12381.ProofSupport.Fp.modulusHi).toNat ≠ 0 := by
      simp only [not_ne_iff]
      rw [← hrepair, hc]
      rfl
    unfold fpSubValue Challenge.Bls12381.ProofSupport.Fp.subSource
    rw [if_pos hc, if_neg hkeep, hraw]
  · have hdoRepair : (UInt256.gt
        (Challenge.Bls12381.ProofSupport.Fp.subRaw a b).hi
          Challenge.Bls12381.ProofSupport.Fp.modulusHi).toNat ≠ 0 := by
      intro hzero
      have hnat := congrArg UInt256.toNat hrepair
      rw [hzero] at hnat
      apply hc
      apply BitVec.toNat_injective
      simpa using hnat
    unfold fpSubValue Challenge.Bls12381.ProofSupport.Fp.subSource
    rw [if_neg hc, if_pos hdoRepair, conv_fpSubRepairValue, hraw]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
