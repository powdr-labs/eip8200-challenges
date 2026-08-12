import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalX3Defs

set_option warningAsError true

/-! Opaque `fpMul` composition for the unequal-point slope square. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalX3Result (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  fpMulResult (pointAddUnequalLambdaState yst out left right)
    (pointAddUnequalLambdaResult yst out left right).1
    (pointAddUnequalLambdaResult yst out left right).2
    (pointAddUnequalLambdaResult yst out left right).1
    (pointAddUnequalLambdaResult yst out left right).2

def pointAddUnequalX3State (yst : EvmState)
    (out left right : U256) : EvmState :=
  fpMulFinalState (pointAddUnequalLambdaState yst out left right)
    (pointAddUnequalLambdaResult yst out left right).1
    (pointAddUnequalLambdaResult yst out left right).2
    (pointAddUnequalLambdaResult yst out left right).1
    (pointAddUnequalLambdaResult yst out left right).2

def pointAddUnequalX3Env (yst : EvmState)
    (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00136", "\x00137"].zip
    [(pointAddUnequalX3Result yst out left right).1,
      (pointAddUnequalX3Result yst out left right).2] ++
    pointAddUnequalLambdaEnv yst out left right

private theorem lambdaEnv_hi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalLambdaEnv yst out left right) "\x00134" =
      some (pointAddUnequalLambdaResult yst out left right).1 := by
  rfl

private theorem lambdaEnv_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddUnequalLambdaEnv yst out left right) "\x00135" =
      some (pointAddUnequalLambdaResult yst out left right).2 := by
  rfl

theorem step_pointAddUnequalX3 (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalLambdaEnv yst out left right)
      (pointAddUnequalLambdaState yst out left right) pointAddUnequalX3Expr
      (.vals [(pointAddUnequalX3Result yst out left right).1,
        (pointAddUnequalX3Result yst out left right).2]
        (pointAddUnequalX3State yst out left right)) := by
  have hlo2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalLambdaEnv yst out left right)
      (pointAddUnequalLambdaState yst out left right) (.var "\x00135")
      (.vals [(pointAddUnequalLambdaResult yst out left right).2]
        (pointAddUnequalLambdaState yst out left right)) :=
    Step.var (lambdaEnv_lo yst out left right)
  have hhi2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalLambdaEnv yst out left right)
      (pointAddUnequalLambdaState yst out left right) (.var "\x00134")
      (.vals [(pointAddUnequalLambdaResult yst out left right).1]
        (pointAddUnequalLambdaState yst out left right)) :=
    Step.var (lambdaEnv_hi yst out left right)
  have hlo1 := hlo2
  have hhi1 := hhi2
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalLambdaEnv yst out left right)
      (pointAddUnequalLambdaState yst out left right) pointAddUnequalX3Args
      (.vals [(pointAddUnequalLambdaResult yst out left right).1,
        (pointAddUnequalLambdaResult yst out left right).2,
        (pointAddUnequalLambdaResult yst out left right).1,
        (pointAddUnequalLambdaResult yst out left right).2]
        (pointAddUnequalLambdaState yst out left right)) := by
    rw [pointAddUnequalX3Args_eq]
    exact Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hlo2) hhi2)
        hlo1) hhi1
  rw [pointAddUnequalX3Expr_eq]
  exact step_fpMul_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddUnequalX3Stmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalLambdaEnv yst out left right)
      (pointAddUnequalLambdaState yst out left right)
      pointAddUnequalX3Stmt (pointAddUnequalX3Env yst out left right)
      (pointAddUnequalX3State yst out left right) .normal := by
  rw [pointAddUnequalX3Stmt_eq]
  exact Step.letVal (step_pointAddUnequalX3 yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
