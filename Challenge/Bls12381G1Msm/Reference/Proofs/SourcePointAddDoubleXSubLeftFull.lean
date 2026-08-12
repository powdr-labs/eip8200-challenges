import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftOutputs
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftPrefixRepair

set_option warningAsError true

/-! Complete first inlined `fpSub` of the point-doubling x-coordinate. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubLeftEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddDoubleX3Env yst out left right)
    (pointAddDoubleXSubLeftWorkEnv yst out left right)

theorem step_pointAddDoubleXSubLeftStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleX3Env yst out left right)
      (pointAddDoubleX3State yst out left right)
      pointAddDoubleXSubLeftStmt (pointAddDoubleXSubLeftEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddDoubleX3Env yst out left right)
      (pointAddDoubleX3State yst out left right) pointAddDoubleXSubLeftBody
      (pointAddDoubleXSubLeftWorkEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddDoubleXSubLeftBody =
      pointAddDoubleXSubLeftPrefixRepair ++
        [.assign ["\x00122"] (.var "fc0_28"),
         .assign ["\x00123"] (.var "fc0_29")] by rfl]
    exact step_appendNormal (step_pointAddDoubleXSubLeftPrefixRepair yst out left right)
      (step_pointAddDoubleXSubLeftOutputs yst out left right)
  rw [pointAddDoubleXSubLeftStmt_eq]
  exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
