import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaEnvLookup

set_option warningAsError true

/-! Opaque `fpMul` composition for `lambda * (left.x - x3)`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalYMulArgs : List (Expr Op) :=
  [.var "\x00134", .var "\x00135", .var "\x00138", .var "\x00139"]

theorem pointAddUnequalYMulStmt_eq : pointAddUnequalYMulStmt =
    .letDecl ["\x00140", "\x00141"]
      (some (.call "\x009" pointAddUnequalYMulArgs)) := by rfl

def pointAddUnequalYMulResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpMulResult (pointAddUnequalDeltaConcreteState yst out left right)
    (pointAddUnequalLambdaResult yst out left right).1
    (pointAddUnequalLambdaResult yst out left right).2
    (pointAddUnequalDeltaResult
      (pointAddUnequalDeltaContext yst out left right)).1
    (pointAddUnequalDeltaResult
      (pointAddUnequalDeltaContext yst out left right)).2

def pointAddUnequalYMulState (yst : EvmState) (out left right : U256) : EvmState :=
  fpMulFinalState (pointAddUnequalDeltaConcreteState yst out left right)
    (pointAddUnequalLambdaResult yst out left right).1
    (pointAddUnequalLambdaResult yst out left right).2
    (pointAddUnequalDeltaResult
      (pointAddUnequalDeltaContext yst out left right)).1
    (pointAddUnequalDeltaResult
      (pointAddUnequalDeltaContext yst out left right)).2

def pointAddUnequalYMulEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00140", "\x00141"].zip
    [(pointAddUnequalYMulResult yst out left right).1,
     (pointAddUnequalYMulResult yst out left right).2] ++
    pointAddUnequalDeltaConcreteEnv yst out left right

theorem step_pointAddUnequalYMul (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right)
      (.call "\x009" pointAddUnequalYMulArgs)
      (.vals [(pointAddUnequalYMulResult yst out left right).1,
        (pointAddUnequalYMulResult yst out left right).2]
        (pointAddUnequalYMulState yst out left right)) := by
  have hdeltaLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right) (.var "\x00139")
      (.vals [(pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).2]
        (pointAddUnequalDeltaConcreteState yst out left right)) :=
    Step.var (pointAddUnequalDeltaConcreteEnv_lo yst out left right)
  have hdeltaHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right) (.var "\x00138")
      (.vals [(pointAddUnequalDeltaResult
        (pointAddUnequalDeltaContext yst out left right)).1]
        (pointAddUnequalDeltaConcreteState yst out left right)) :=
    Step.var (pointAddUnequalDeltaConcreteEnv_hi yst out left right)
  have hlambdaLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right) (.var "\x00135")
      (.vals [(pointAddUnequalLambdaResult yst out left right).2]
        (pointAddUnequalDeltaConcreteState yst out left right)) :=
    Step.var (pointAddUnequalDeltaConcreteEnv_lambdaLo yst out left right)
  have hlambdaHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right) (.var "\x00134")
      (.vals [(pointAddUnequalLambdaResult yst out left right).1]
        (pointAddUnequalDeltaConcreteState yst out left right)) :=
    Step.var (pointAddUnequalDeltaConcreteEnv_lambdaHi yst out left right)
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right)
      pointAddUnequalYMulArgs
      (.vals [(pointAddUnequalLambdaResult yst out left right).1,
        (pointAddUnequalLambdaResult yst out left right).2,
        (pointAddUnequalDeltaResult
          (pointAddUnequalDeltaContext yst out left right)).1,
        (pointAddUnequalDeltaResult
          (pointAddUnequalDeltaContext yst out left right)).2]
        (pointAddUnequalDeltaConcreteState yst out left right)) :=
    Step.argsCons
      (Step.argsCons (Step.argsCons
        (Step.argsCons Step.argsNil hdeltaLo) hdeltaHi) hlambdaLo) hlambdaHi
  exact step_fpMul_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddUnequalYMulStmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right)
      pointAddUnequalYMulStmt (pointAddUnequalYMulEnv yst out left right)
      (pointAddUnequalYMulState yst out left right) .normal := by
  rw [pointAddUnequalYMulStmt_eq]
  exact Step.letVal (step_pointAddUnequalYMul yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
