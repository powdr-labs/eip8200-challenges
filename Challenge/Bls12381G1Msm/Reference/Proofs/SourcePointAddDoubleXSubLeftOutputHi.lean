import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftSelected
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! First output assignment of the first point-double subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddDoubleXSubLeftOutputHiExplicit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftSelectedEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.assign ["\x00122"] (.var "fc0_28"))
      (VEnv.set (pointAddDoubleXSubLeftSelectedEnv yst out left right)
        "\x00122" (pointAddDoubleXSubLeftResult yst out left right).1)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal :=
  step_assignVar (pointAddDoubleXSubLeftSelectedEnv_hi yst out left right)

def pointAddDoubleXSubLeftHighEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubLeftSelectedEnv yst out left right)
    "\x00122" (pointAddDoubleXSubLeftResult yst out left right).1

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
