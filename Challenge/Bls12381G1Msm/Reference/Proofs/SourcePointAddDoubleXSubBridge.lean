import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFunEnvInsert

set_option warningAsError true

/-! Single bridge from the concrete first subtraction to the generic second one. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubRightContext (yst : EvmState)
    (out left right : U256) : PointAddDoubleXSubRightContext where
  env := pointAddDoubleXSubLeftEnv yst out left right
  state := pointAddDoubleXSubLeftRawState yst out left right
  x3Hi := (pointAddDoubleXSubLeftResult yst out left right).1
  x3Lo := (pointAddDoubleXSubLeftResult yst out left right).2
  env_hi := pointAddDoubleXSubLeftEnv_hi yst out left right
  env_lo := pointAddDoubleXSubLeftEnv_lo yst out left right

def pointAddDoubleXSubEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddDoubleX3Env yst out left right)
    (pointAddDoubleXSubRightWorkEnv
      (pointAddDoubleXSubRightContext yst out left right))

def pointAddDoubleXSubState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddDoubleXSubRightRawState
    (pointAddDoubleXSubRightContext yst out left right)

theorem step_pointAddDoubleXSubStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleX3Env yst out left right)
      (pointAddDoubleX3State yst out left right) pointAddDoubleXSubStmt
      (pointAddDoubleXSubEnv yst out left right)
      (pointAddDoubleXSubState yst out left right) .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleX3Env yst out left right)
      (pointAddDoubleX3State yst out left right) pointAddDoubleXSubBody
      (pointAddDoubleXSubRightWorkEnv
        (pointAddDoubleXSubRightContext yst out left right))
      (pointAddDoubleXSubState yst out left right) .normal := by
    rw [pointAddDoubleXSubBody_eq]
    have hleft := step_funEnvInsert
      (step_pointAddDoubleXSubLeftStmt yst out left right)
      (FunEnvInsertEmpty.here pointAddBodyFuns)
    exact Step.seqCons hleft
      (step_pointAddDoubleXSubRightGeneric
        (pointAddDoubleXSubRightContext yst out left right))
  rw [pointAddDoubleXSubStmt_eq]
  exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
