import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSqCall

set_option warningAsError true

/-! Pure `2 * x²` numerator step in point doubling. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleNum2Result (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpAddResult (pointAddDoubleXSqResult yst out left right).1
    (pointAddDoubleXSqResult yst out left right).2
    (pointAddDoubleXSqResult yst out left right).1
    (pointAddDoubleXSqResult yst out left right).2

def pointAddDoubleNum2Env (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00114", "\x00115"].zip
    [(pointAddDoubleNum2Result yst out left right).1,
      (pointAddDoubleNum2Result yst out left right).2] ++
    pointAddDoubleXSqEnv yst out left right

private theorem xsqEnv_hi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleXSqEnv yst out left right) "\x00112" =
      some (pointAddDoubleXSqResult yst out left right).1 := by
  rfl

private theorem xsqEnv_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleXSqEnv yst out left right) "\x00113" =
      some (pointAddDoubleXSqResult yst out left right).2 := by
  rfl

theorem step_pointAddDoubleNum2 (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleXSqEnv yst out left right)
      (pointAddDoubleXSqState yst out left right) pointAddDoubleNum2Expr
      (.vals [(pointAddDoubleNum2Result yst out left right).1,
        (pointAddDoubleNum2Result yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) := by
  have hlo2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleXSqEnv yst out left right)
      (pointAddDoubleXSqState yst out left right) (.var "\x00113")
      (.vals [(pointAddDoubleXSqResult yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.var (xsqEnv_lo yst out left right)
  have hhi2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleXSqEnv yst out left right)
      (pointAddDoubleXSqState yst out left right) (.var "\x00112")
      (.vals [(pointAddDoubleXSqResult yst out left right).1]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.var (xsqEnv_hi yst out left right)
  have hlo1 := hlo2
  have hhi1 := hhi2
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleXSqEnv yst out left right)
      (pointAddDoubleXSqState yst out left right)
      [.var "\x00112", .var "\x00113", .var "\x00112", .var "\x00113"]
      (.vals [(pointAddDoubleXSqResult yst out left right).1,
        (pointAddDoubleXSqResult yst out left right).2,
        (pointAddDoubleXSqResult yst out left right).1,
        (pointAddDoubleXSqResult yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) :=
    Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hlo2) hhi2)
        hlo1) hhi1
  rw [pointAddDoubleNum2Expr_eq]
  exact step_fpAdd_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddDoubleNum2Stmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleXSqEnv yst out left right)
      (pointAddDoubleXSqState yst out left right) pointAddDoubleNum2Stmt
      (pointAddDoubleNum2Env yst out left right)
      (pointAddDoubleXSqState yst out left right) .normal := by
  rw [pointAddDoubleNum2Stmt_eq]
  exact Step.letVal (step_pointAddDoubleNum2 yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
