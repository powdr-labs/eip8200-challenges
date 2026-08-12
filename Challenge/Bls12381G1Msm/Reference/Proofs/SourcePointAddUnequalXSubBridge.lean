import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFunEnvInsert

set_option warningAsError true

/-! Single bridge from the concrete first subtraction to the generic second one. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubRightContext (yst : EvmState)
    (out left right : U256) : PointAddUnequalXSubRightContext :=
  makePointAddUnequalXSubRightContext
    (pointAddUnequalXSubLeftEnv yst out left right)
    (pointAddUnequalXSubLeftRawState yst out left right)
    (pointAddUnequalXSubLeftResult yst out left right).1
    (pointAddUnequalXSubLeftResult yst out left right).2
    (pointAddUnequalXSubLeftEnv_hi yst out left right)
    (pointAddUnequalXSubLeftEnv_lo yst out left right)

def pointAddUnequalXSubEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddUnequalX3Env yst out left right)
    (pointAddUnequalXSubRightWorkEnv
      (pointAddUnequalXSubRightContext yst out left right))

def pointAddUnequalXSubState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddUnequalXSubRightRawState
    (pointAddUnequalXSubRightContext yst out left right)

theorem step_pointAddUnequalXSubStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalX3Env yst out left right)
      (pointAddUnequalX3State yst out left right) pointAddUnequalXSubStmt
      (pointAddUnequalXSubEnv yst out left right)
      (pointAddUnequalXSubState yst out left right) .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalX3Env yst out left right)
      (pointAddUnequalX3State yst out left right) pointAddUnequalXSubBody
      (pointAddUnequalXSubRightWorkEnv
        (pointAddUnequalXSubRightContext yst out left right))
      (pointAddUnequalXSubState yst out left right) .normal := by
    rw [pointAddUnequalXSubBody_eq]
    have hleft := step_funEnvInsert
      (step_pointAddUnequalXSubLeftStmt yst out left right)
      (FunEnvInsertEmpty.here pointAddBodyFuns)
    exact Step.seqCons hleft
      (step_pointAddUnequalXSubRightGeneric
        (pointAddUnequalXSubRightContext yst out left right))
  rw [pointAddUnequalXSubStmt_eq]
  exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
