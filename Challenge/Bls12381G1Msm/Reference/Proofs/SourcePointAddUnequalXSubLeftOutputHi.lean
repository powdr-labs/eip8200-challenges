import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftSelected
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! First output assignment of the first unequal-point subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalXSubLeftOutputHiExplicit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftSelectedEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.assign ["\x00136"] (.var "fc0_81"))
      (VEnv.set (pointAddUnequalXSubLeftSelectedEnv yst out left right)
        "\x00136" (pointAddUnequalXSubLeftResult yst out left right).1)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal :=
  step_assignVar (pointAddUnequalXSubLeftSelectedEnv_hi yst out left right)

def pointAddUnequalXSubLeftHighEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubLeftSelectedEnv yst out left right)
    "\x00136" (pointAddUnequalXSubLeftResult yst out left right).1

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
