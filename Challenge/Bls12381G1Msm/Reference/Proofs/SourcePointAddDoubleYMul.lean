import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaEnvLookup

set_option warningAsError true

/-! Opaque `fpMul` composition for `lambda * (left.x - x3)`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYMulArgs : List (Expr Op) :=
  [.var "\x00120", .var "\x00121", .var "\x00124", .var "\x00125"]

theorem pointAddDoubleYMulStmt_eq : pointAddDoubleYMulStmt =
    .letDecl ["\x00126", "\x00127"]
      (some (.call "\x009" pointAddDoubleYMulArgs)) := by rfl

def pointAddDoubleYMulResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpMulResult (pointAddDoubleDeltaConcreteState yst out left right)
    (pointAddDoubleLambdaResult yst out left right).1
    (pointAddDoubleLambdaResult yst out left right).2
    (pointAddDoubleDeltaResult
      (pointAddDoubleDeltaContext yst out left right)).1
    (pointAddDoubleDeltaResult
      (pointAddDoubleDeltaContext yst out left right)).2

def pointAddDoubleYMulState (yst : EvmState) (out left right : U256) : EvmState :=
  fpMulFinalState (pointAddDoubleDeltaConcreteState yst out left right)
    (pointAddDoubleLambdaResult yst out left right).1
    (pointAddDoubleLambdaResult yst out left right).2
    (pointAddDoubleDeltaResult
      (pointAddDoubleDeltaContext yst out left right)).1
    (pointAddDoubleDeltaResult
      (pointAddDoubleDeltaContext yst out left right)).2

def pointAddDoubleYMulEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00126", "\x00127"].zip
    [(pointAddDoubleYMulResult yst out left right).1,
     (pointAddDoubleYMulResult yst out left right).2] ++
    pointAddDoubleDeltaConcreteEnv yst out left right

theorem step_pointAddDoubleYMul (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right)
      (.call "\x009" pointAddDoubleYMulArgs)
      (.vals [(pointAddDoubleYMulResult yst out left right).1,
        (pointAddDoubleYMulResult yst out left right).2]
        (pointAddDoubleYMulState yst out left right)) := by
  have hdeltaLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right) (.var "\x00125")
      (.vals [(pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).2]
        (pointAddDoubleDeltaConcreteState yst out left right)) :=
    Step.var (pointAddDoubleDeltaConcreteEnv_lo yst out left right)
  have hdeltaHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right) (.var "\x00124")
      (.vals [(pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).1]
        (pointAddDoubleDeltaConcreteState yst out left right)) :=
    Step.var (pointAddDoubleDeltaConcreteEnv_hi yst out left right)
  have hlambdaLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right) (.var "\x00121")
      (.vals [(pointAddDoubleLambdaResult yst out left right).2]
        (pointAddDoubleDeltaConcreteState yst out left right)) :=
    Step.var (pointAddDoubleDeltaConcreteEnv_lambdaLo yst out left right)
  have hlambdaHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right) (.var "\x00120")
      (.vals [(pointAddDoubleLambdaResult yst out left right).1]
        (pointAddDoubleDeltaConcreteState yst out left right)) :=
    Step.var (pointAddDoubleDeltaConcreteEnv_lambdaHi yst out left right)
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right)
      pointAddDoubleYMulArgs
      (.vals [(pointAddDoubleLambdaResult yst out left right).1,
        (pointAddDoubleLambdaResult yst out left right).2,
        (pointAddDoubleDeltaResult
          (pointAddDoubleDeltaContext yst out left right)).1,
        (pointAddDoubleDeltaResult
          (pointAddDoubleDeltaContext yst out left right)).2]
        (pointAddDoubleDeltaConcreteState yst out left right)) :=
    Step.argsCons
      (Step.argsCons (Step.argsCons
        (Step.argsCons Step.argsNil hdeltaLo) hdeltaHi) hlambdaLo) hlambdaHi
  exact step_fpMul_of_args _ _ _ _ hargs (by rfl)

theorem step_pointAddDoubleYMulStmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right)
      pointAddDoubleYMulStmt (pointAddDoubleYMulEnv yst out left right)
      (pointAddDoubleYMulState yst out left right) .normal := by
  rw [pointAddDoubleYMulStmt_eq]
  exact Step.letVal (step_pointAddDoubleYMul yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
