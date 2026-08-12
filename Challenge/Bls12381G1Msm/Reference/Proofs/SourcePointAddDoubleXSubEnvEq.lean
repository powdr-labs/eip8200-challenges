import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubBridge

set_option warningAsError true

/-! Opaque final environment equality after both point-double x subtractions. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  pointAddDoubleXSubRightResult
    (pointAddDoubleXSubRightContext yst out left right)

theorem pointAddDoubleXSubEnv_eq (yst : EvmState)
    (out left right : U256) :
    pointAddDoubleXSubEnv yst out left right =
      VEnv.set
        (VEnv.set (pointAddDoubleXSubLeftEnv yst out left right) "\x00122"
          (pointAddDoubleXSubResult yst out left right).1)
        "\x00123" (pointAddDoubleXSubResult yst out left right).2 := by
  rw [pointAddDoubleXSubEnv, pointAddDoubleXSubRightWorkEnv,
    pointAddDoubleXSubRightHighOutEnv,
    pointAddDoubleXSubRightSelectedEnv]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]
  change (pointAddDoubleXSubLeftEnv yst out left right).length = _
  rw [pointAddDoubleXSubLeftEnv_eq, venv_set_length, venv_set_length]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
