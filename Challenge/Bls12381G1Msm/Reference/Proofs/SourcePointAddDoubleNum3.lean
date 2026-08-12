import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleNum2

set_option warningAsError true

/-! Pure `3 * x²` numerator step in point doubling. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleNum3Result (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpAddResult (pointAddDoubleNum2Result yst out left right).1
    (pointAddDoubleNum2Result yst out left right).2
    (pointAddDoubleXSqResult yst out left right).1
    (pointAddDoubleXSqResult yst out left right).2

def pointAddDoubleNum3Env (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (pointAddDoubleNum2Env yst out left right)
    ["\x00114", "\x00115"]
    [(pointAddDoubleNum3Result yst out left right).1,
      (pointAddDoubleNum3Result yst out left right).2]

private theorem num2Env_numHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleNum2Env yst out left right) "\x00114" =
      some (pointAddDoubleNum2Result yst out left right).1 := by rfl

private theorem num2Env_numLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleNum2Env yst out left right) "\x00115" =
      some (pointAddDoubleNum2Result yst out left right).2 := by rfl

private theorem num2Env_xHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleNum2Env yst out left right) "\x00112" =
      some (pointAddDoubleXSqResult yst out left right).1 := by rfl

private theorem num2Env_xLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleNum2Env yst out left right) "\x00113" =
      some (pointAddDoubleXSqResult yst out left right).2 := by rfl

theorem step_pointAddDoubleNum3 (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right) pointAddDoubleNum3Expr
      (.vals [(pointAddDoubleNum3Result yst out left right).1,
        (pointAddDoubleNum3Result yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) := by
  have hxlo : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right) (.var "\x00113")
      (.vals [(pointAddDoubleXSqResult yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.var (num2Env_xLo yst out left right)
  have hxhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right) (.var "\x00112")
      (.vals [(pointAddDoubleXSqResult yst out left right).1]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.var (num2Env_xHi yst out left right)
  have hnlo : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right) (.var "\x00115")
      (.vals [(pointAddDoubleNum2Result yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.var (num2Env_numLo yst out left right)
  have hnhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right) (.var "\x00114")
      (.vals [(pointAddDoubleNum2Result yst out left right).1]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.var (num2Env_numHi yst out left right)
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right)
      [.var "\x00114", .var "\x00115", .var "\x00112", .var "\x00113"]
      (.vals [(pointAddDoubleNum2Result yst out left right).1,
        (pointAddDoubleNum2Result yst out left right).2,
        (pointAddDoubleXSqResult yst out left right).1,
        (pointAddDoubleXSqResult yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hxlo) hxhi)
        hnlo) hnhi
  rw [pointAddDoubleNum3Expr_eq]
  exact step_fpAdd_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddDoubleNum3Stmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right) pointAddDoubleNum3Stmt
      (pointAddDoubleNum3Env yst out left right)
      (pointAddDoubleXSqState yst out left right) .normal := by
  rw [pointAddDoubleNum3Stmt_eq]
  exact Step.assignVal (step_pointAddDoubleNum3 yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
