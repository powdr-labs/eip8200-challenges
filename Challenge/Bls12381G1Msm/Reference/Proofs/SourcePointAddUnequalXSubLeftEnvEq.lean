import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftEnvShape
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Opaque restored-environment equality after the first unequal-point subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalXSubLeftEnv_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalXSubLeftEnv yst out left right =
      VEnv.set
        (VEnv.set (pointAddUnequalX3Env yst out left right) "\x00136"
          (pointAddUnequalXSubLeftResult yst out left right).1)
        "\x00137" (pointAddUnequalXSubLeftResult yst out left right).2 := by
  rcases pointAddUnequalXSubLeftSelectedEnv_shape yst out left right with
    ⟨localHi, localLo, hshape⟩
  rw [pointAddUnequalXSubLeftEnv, pointAddUnequalXSubLeftWorkEnv,
    pointAddUnequalXSubLeftHighEnv, hshape]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
