import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftEnvShape
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Opaque restored-environment equality after the first point-double subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddDoubleXSubLeftEnv_eq (yst : EvmState)
    (out left right : U256) :
    pointAddDoubleXSubLeftEnv yst out left right =
      VEnv.set
        (VEnv.set (pointAddDoubleX3Env yst out left right) "\x00122"
          (pointAddDoubleXSubLeftResult yst out left right).1)
        "\x00123" (pointAddDoubleXSubLeftResult yst out left right).2 := by
  rcases pointAddDoubleXSubLeftSelectedEnv_shape yst out left right with
    ⟨localHi, localLo, hshape⟩
  rw [pointAddDoubleXSubLeftEnv, pointAddDoubleXSubLeftWorkEnv,
    pointAddDoubleXSubLeftHighEnv, hshape]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
