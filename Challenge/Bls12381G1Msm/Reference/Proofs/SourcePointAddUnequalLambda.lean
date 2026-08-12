import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalLambdaDefs
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvOutputLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

/-! Opaque `fpMul` composition for the unequal-point slope. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalLambdaResult (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  fpMulResult (pointAddUnequalInvFinalState yst out left right)
    (pointAddUnequalNumeratorResult yst out left right).1
    (pointAddUnequalNumeratorResult yst out left right).2
    (pointAddUnequalInvResult yst out left right).1
    (pointAddUnequalInvResult yst out left right).2

def pointAddUnequalLambdaState (yst : EvmState)
    (out left right : U256) : EvmState :=
  fpMulFinalState (pointAddUnequalInvFinalState yst out left right)
    (pointAddUnequalNumeratorResult yst out left right).1
    (pointAddUnequalNumeratorResult yst out left right).2
    (pointAddUnequalInvResult yst out left right).1
    (pointAddUnequalInvResult yst out left right).2

def pointAddUnequalLambdaEnv (yst : EvmState)
    (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00134", "\x00135"].zip
    [(pointAddUnequalLambdaResult yst out left right).1,
      (pointAddUnequalLambdaResult yst out left right).2] ++
    pointAddUnequalInvOutputEnv yst out left right

theorem step_pointAddUnequalLambda (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right)
      pointAddUnequalLambdaExpr
      (.vals [(pointAddUnequalLambdaResult yst out left right).1,
        (pointAddUnequalLambdaResult yst out left right).2]
        (pointAddUnequalLambdaState yst out left right)) := by
  have hinvLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right) (.var "\x00133")
      (.vals [(pointAddUnequalInvResult yst out left right).2]
        (pointAddUnequalInvFinalState yst out left right)) :=
    Step.var (pointAddUnequalInvOutputEnv_invLo yst out left right)
  have hinvHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right) (.var "\x00132")
      (.vals [(pointAddUnequalInvResult yst out left right).1]
        (pointAddUnequalInvFinalState yst out left right)) :=
    Step.var (pointAddUnequalInvOutputEnv_invHi yst out left right)
  have hnumLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right) (.var "\x00129")
      (.vals [(pointAddUnequalNumeratorResult yst out left right).2]
        (pointAddUnequalInvFinalState yst out left right)) :=
    Step.var (pointAddUnequalInvOutputEnv_numLo yst out left right)
  have hnumHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right) (.var "\x00128")
      (.vals [(pointAddUnequalNumeratorResult yst out left right).1]
        (pointAddUnequalInvFinalState yst out left right)) :=
    Step.var (pointAddUnequalInvOutputEnv_numHi yst out left right)
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right)
      pointAddUnequalLambdaArgs
      (.vals [(pointAddUnequalNumeratorResult yst out left right).1,
        (pointAddUnequalNumeratorResult yst out left right).2,
        (pointAddUnequalInvResult yst out left right).1,
        (pointAddUnequalInvResult yst out left right).2]
        (pointAddUnequalInvFinalState yst out left right)) := by
    rw [pointAddUnequalLambdaArgs_eq]
    exact Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hinvLo) hinvHi)
        hnumLo) hnumHi
  rw [pointAddUnequalLambdaExpr_eq]
  exact step_fpMul_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddUnequalLambdaStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalInvOutputEnv yst out left right)
      (pointAddUnequalInvFinalState yst out left right)
      pointAddUnequalLambdaStmt
      (pointAddUnequalLambdaEnv yst out left right)
      (pointAddUnequalLambdaState yst out left right) .normal := by
  rw [pointAddUnequalLambdaStmt_eq]
  exact Step.letVal (step_pointAddUnequalLambda yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
