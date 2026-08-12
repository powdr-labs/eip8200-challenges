import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleLambda

set_option warningAsError true

/-! Opaque `fpMul` composition for the initial point-doubling x-coordinate. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleX3Result (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpMulResult (pointAddDoubleLambdaState yst out left right)
    (pointAddDoubleLambdaResult yst out left right).1
    (pointAddDoubleLambdaResult yst out left right).2
    (pointAddDoubleLambdaResult yst out left right).1
    (pointAddDoubleLambdaResult yst out left right).2

def pointAddDoubleX3State (yst : EvmState) (out left right : U256) : EvmState :=
  fpMulFinalState (pointAddDoubleLambdaState yst out left right)
    (pointAddDoubleLambdaResult yst out left right).1
    (pointAddDoubleLambdaResult yst out left right).2
    (pointAddDoubleLambdaResult yst out left right).1
    (pointAddDoubleLambdaResult yst out left right).2

def pointAddDoubleX3Env (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00122", "\x00123"].zip
    [(pointAddDoubleX3Result yst out left right).1,
      (pointAddDoubleX3Result yst out left right).2] ++
    pointAddDoubleLambdaEnv yst out left right

private theorem lambdaEnv_hi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleLambdaEnv yst out left right) "\x00120" =
      some (pointAddDoubleLambdaResult yst out left right).1 := by
  rfl

private theorem lambdaEnv_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleLambdaEnv yst out left right) "\x00121" =
      some (pointAddDoubleLambdaResult yst out left right).2 := by
  rfl

theorem step_pointAddDoubleX3 (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleLambdaEnv yst out left right)
      (pointAddDoubleLambdaState yst out left right) pointAddDoubleX3Expr
      (.vals [(pointAddDoubleX3Result yst out left right).1,
        (pointAddDoubleX3Result yst out left right).2]
        (pointAddDoubleX3State yst out left right)) := by
  have hlo2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleLambdaEnv yst out left right)
      (pointAddDoubleLambdaState yst out left right) (.var "\x00121")
      (.vals [(pointAddDoubleLambdaResult yst out left right).2]
        (pointAddDoubleLambdaState yst out left right)) :=
    Step.var (lambdaEnv_lo yst out left right)
  have hhi2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleLambdaEnv yst out left right)
      (pointAddDoubleLambdaState yst out left right) (.var "\x00120")
      (.vals [(pointAddDoubleLambdaResult yst out left right).1]
        (pointAddDoubleLambdaState yst out left right)) :=
    Step.var (lambdaEnv_hi yst out left right)
  have hlo1 := hlo2
  have hhi1 := hhi2
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleLambdaEnv yst out left right)
      (pointAddDoubleLambdaState yst out left right) pointAddDoubleX3Args
      (.vals [(pointAddDoubleLambdaResult yst out left right).1,
        (pointAddDoubleLambdaResult yst out left right).2,
        (pointAddDoubleLambdaResult yst out left right).1,
        (pointAddDoubleLambdaResult yst out left right).2]
        (pointAddDoubleLambdaState yst out left right)) := by
    rw [pointAddDoubleX3Args_eq]
    exact Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hlo2) hhi2)
        hlo1) hhi1
  rw [pointAddDoubleX3Expr_eq]
  exact step_fpMul_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddDoubleX3Stmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleLambdaEnv yst out left right)
      (pointAddDoubleLambdaState yst out left right) pointAddDoubleX3Stmt
      (pointAddDoubleX3Env yst out left right)
      (pointAddDoubleX3State yst out left right) .normal := by
  rw [pointAddDoubleX3Stmt_eq]
  exact Step.letVal (step_pointAddDoubleX3 yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
