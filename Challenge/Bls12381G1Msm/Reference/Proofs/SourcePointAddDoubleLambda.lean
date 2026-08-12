import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleInvOutput
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

/-! Opaque `fpMul` composition for the point-doubling slope. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleLambdaResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpMulResult (pointAddDoubleInvFinalState yst out left right)
    (pointAddDoubleNum3Result yst out left right).1
    (pointAddDoubleNum3Result yst out left right).2
    (pointAddDoubleInvResult yst out left right).1
    (pointAddDoubleInvResult yst out left right).2

def pointAddDoubleLambdaState (yst : EvmState) (out left right : U256) : EvmState :=
  fpMulFinalState (pointAddDoubleInvFinalState yst out left right)
    (pointAddDoubleNum3Result yst out left right).1
    (pointAddDoubleNum3Result yst out left right).2
    (pointAddDoubleInvResult yst out left right).1
    (pointAddDoubleInvResult yst out left right).2

def pointAddDoubleLambdaEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00120", "\x00121"].zip
    [(pointAddDoubleLambdaResult yst out left right).1,
      (pointAddDoubleLambdaResult yst out left right).2] ++
    pointAddDoubleInvOutputEnv yst out left right

private theorem invEnv_numHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleInvOutputEnv yst out left right) "\x00114" =
      some (pointAddDoubleNum3Result yst out left right).1 := by
  rfl

private theorem invEnv_numLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleInvOutputEnv yst out left right) "\x00115" =
      some (pointAddDoubleNum3Result yst out left right).2 := by
  rfl

private theorem invEnv_invHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleInvOutputEnv yst out left right) "\x00118" =
      some (pointAddDoubleInvResult yst out left right).1 := by
  rfl

private theorem invEnv_invLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleInvOutputEnv yst out left right) "\x00119" =
      some (pointAddDoubleInvResult yst out left right).2 := by
  rfl

theorem step_pointAddDoubleLambda (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right)
      pointAddDoubleLambdaExpr
      (.vals [(pointAddDoubleLambdaResult yst out left right).1,
        (pointAddDoubleLambdaResult yst out left right).2]
        (pointAddDoubleLambdaState yst out left right)) := by
  have hinvLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) (.var "\x00119")
      (.vals [(pointAddDoubleInvResult yst out left right).2]
        (pointAddDoubleInvFinalState yst out left right)) :=
    Step.var (invEnv_invLo yst out left right)
  have hinvHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) (.var "\x00118")
      (.vals [(pointAddDoubleInvResult yst out left right).1]
        (pointAddDoubleInvFinalState yst out left right)) :=
    Step.var (invEnv_invHi yst out left right)
  have hnumLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) (.var "\x00115")
      (.vals [(pointAddDoubleNum3Result yst out left right).2]
        (pointAddDoubleInvFinalState yst out left right)) :=
    Step.var (invEnv_numLo yst out left right)
  have hnumHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) (.var "\x00114")
      (.vals [(pointAddDoubleNum3Result yst out left right).1]
        (pointAddDoubleInvFinalState yst out left right)) :=
    Step.var (invEnv_numHi yst out left right)
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right) pointAddDoubleLambdaArgs
      (.vals [(pointAddDoubleNum3Result yst out left right).1,
        (pointAddDoubleNum3Result yst out left right).2,
        (pointAddDoubleInvResult yst out left right).1,
        (pointAddDoubleInvResult yst out left right).2]
        (pointAddDoubleInvFinalState yst out left right)) := by
    rw [pointAddDoubleLambdaArgs_eq]
    exact Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hinvLo) hinvHi)
        hnumLo) hnumHi
  rw [pointAddDoubleLambdaExpr_eq]
  exact step_fpMul_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddDoubleLambdaStmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleInvOutputEnv yst out left right)
      (pointAddDoubleInvFinalState yst out left right)
      pointAddDoubleLambdaStmt (pointAddDoubleLambdaEnv yst out left right)
      (pointAddDoubleLambdaState yst out left right) .normal := by
  rw [pointAddDoubleLambdaStmt_eq]
  exact Step.letVal (step_pointAddDoubleLambda yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
