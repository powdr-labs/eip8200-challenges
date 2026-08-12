import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalX3Math

set_option warningAsError true

/-! Field refinement of the first unequal X subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddUnequalXSubLeftResultLimbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  pointAddUnequalLimbsOfWords
    (pointAddUnequalXSubLeftResult yst out left right)

theorem pointAddUnequalXSubLeftResult_eq_fpSubValue (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalXSubLeftResult yst out left right =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
        (pointAddUnequalX3Result yst out left right).1
        (pointAddUnequalX3Result yst out left right).2
        (pointAddUnequalXSubLeftHi yst out left right)
        (pointAddUnequalXSubLeftLo yst out left right) := by
  rw [pointAddUnequalXSubLeftResult,
    pointAddUnequalXSubLeftRepairValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue,
    pointAddUnequalXSubLeftRepaired_eq_fpSubRepairValue,
    pointAddUnequalXSubLeftRaw_eq_fpSubRawValue]

theorem pointAddUnequalXSubLeftResult_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalXSubLeftResultLimbs yst out left right =
      Fp.subSource (pointAddUnequalX3Limbs yst out left right)
        (pointAddUnequalXSubLeftLimbs yst out left right) := by
  rw [pointAddUnequalXSubLeftResultLimbs,
    pointAddUnequalXSubLeftResult_eq_fpSubValue]
  simpa only [pointAddUnequalLimbsOfWords, pointAddUnequalX3Limbs,
    pointAddUnequalXSubLeftLimbs,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.convPair]
    using Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubValue
      (pointAddUnequalX3Result yst out left right).1
      (pointAddUnequalX3Result yst out left right).2
      (pointAddUnequalXSubLeftHi yst out left right)
      (pointAddUnequalXSubLeftLo yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
