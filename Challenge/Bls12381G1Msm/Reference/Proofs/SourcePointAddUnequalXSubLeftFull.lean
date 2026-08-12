import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftOutputs
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftPrefixRepair

set_option warningAsError true

/-! Complete first inlined `fpSub` of the unequal-point x-coordinate. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubLeftEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddUnequalX3Env yst out left right)
    (pointAddUnequalXSubLeftWorkEnv yst out left right)

theorem step_pointAddUnequalXSubLeftStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalX3Env yst out left right)
      (pointAddUnequalX3State yst out left right)
      pointAddUnequalXSubLeftStmt (pointAddUnequalXSubLeftEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalX3Env yst out left right)
      (pointAddUnequalX3State yst out left right) pointAddUnequalXSubLeftBody
      (pointAddUnequalXSubLeftWorkEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddUnequalXSubLeftBody =
      pointAddUnequalXSubLeftPrefixRepair ++
        [.assign ["\x00136"] (.var "fc0_81"),
         .assign ["\x00137"] (.var "fc0_82")] by rfl]
    exact step_appendNormal (step_pointAddUnequalXSubLeftPrefixRepair yst out left right)
      (step_pointAddUnequalXSubLeftOutputs yst out left right)
  rw [pointAddUnequalXSubLeftStmt_eq]
  exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
