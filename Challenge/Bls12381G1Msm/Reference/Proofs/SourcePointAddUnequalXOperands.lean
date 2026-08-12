import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalMemoryViews

set_option warningAsError true

/-! Original X-coordinate views at the two unequal subtraction sites. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddUnequalXSubLeftLimbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv
      (pointAddUnequalXSubLeftHi yst out left right)
    lo := YulEvmCompiler.conv
      (pointAddUnequalXSubLeftLo yst out left right) }

def pointAddUnequalXSubRightLimbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  let ctx := pointAddUnequalXSubRightContext yst out left right
  { hi := YulEvmCompiler.conv (pointAddUnequalXSubRightHi ctx)
    lo := YulEvmCompiler.conv (pointAddUnequalXSubRightLo ctx) }

theorem pointAddUnequalXSubLeftLimbs_eq (yst : EvmState)
    (out left right : U256)
    (hhi : 1632 ≤ left.toNat) (hlo : 1632 ≤ (left + 32).toNat) :
    pointAddUnequalXSubLeftLimbs yst out left right =
      pointMemoryX yst left := by
  rw [pointAddUnequalXSubLeftLimbs, pointMemoryX]
  simp only [pointAddUnequalXSubLeftHi, pointAddUnequalXSubLeftLo,
    pointAddUnequalXSubLeftPtr_eq]
  rw [pointAddUnequalX3State_loadWord_after_scratch _ _ _ _
      left.toNat (by omega),
    pointAddUnequalX3State_loadWord_after_scratch _ _ _ _
      (left + 32).toNat (by omega),
    pointAddPrefix_loadPoint yst out left right left.toNat hhi,
    pointAddPrefix_loadPoint yst out left right (left + 32).toNat hlo]

theorem pointAddUnequalXSubRightLimbs_eq (yst : EvmState)
    (out left right : U256)
    (hhi : 1632 ≤ right.toNat) (hlo : 1632 ≤ (right + 32).toNat) :
    pointAddUnequalXSubRightLimbs yst out left right =
      pointMemoryX yst right := by
  rw [pointAddUnequalXSubRightLimbs, pointMemoryX]
  simp only [pointAddUnequalXSubRightHi, pointAddUnequalXSubRightLo,
    pointAddUnequalXSubRightPtr_eq]
  rw [show (pointAddUnequalXSubRightContext yst out left right).state =
      pointAddUnequalXSubLeftRawState yst out left right by rfl,
    pointAddUnequalXSubLeftRawState_memory,
    pointAddUnequalX3State_loadWord_after_scratch _ _ _ _
      right.toNat (by omega),
    pointAddUnequalX3State_loadWord_after_scratch _ _ _ _
      (right + 32).toNat (by omega),
    pointAddPrefix_loadPoint yst out left right right.toNat hhi,
    pointAddPrefix_loadPoint yst out left right (right + 32).toNat hlo]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
