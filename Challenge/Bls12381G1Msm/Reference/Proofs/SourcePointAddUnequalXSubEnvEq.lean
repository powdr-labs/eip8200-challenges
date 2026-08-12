import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubBridge

set_option warningAsError true

/-! Opaque final environment equality after both unequal-point x subtractions. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  pointAddUnequalXSubRightResult
    (pointAddUnequalXSubRightContext yst out left right)

theorem pointAddUnequalXSubEnv_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalXSubEnv yst out left right =
      VEnv.set
        (VEnv.set (pointAddUnequalXSubLeftEnv yst out left right) "\x00136"
          (pointAddUnequalXSubResult yst out left right).1)
        "\x00137" (pointAddUnequalXSubResult yst out left right).2 := by
  rw [pointAddUnequalXSubEnv, pointAddUnequalXSubRightWorkEnv,
    pointAddUnequalXSubRightHighOutEnv,
    pointAddUnequalXSubRightSelectedEnv]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]
  change (pointAddUnequalXSubLeftEnv yst out left right).length = _
  rw [pointAddUnequalXSubLeftEnv_eq, venv_set_length, venv_set_length]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
