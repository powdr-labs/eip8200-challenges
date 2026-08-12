import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSq

set_option warningAsError true

/-! Opaque `fpMul` composition for the point-doubling x-square. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSqResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpMulResult (pointAddDoubleXSqArgsState yst out left right)
    (pointAddFiniteLeftXHi yst out left right)
    (pointAddFiniteLeftXLo yst out left right)
    (pointAddFiniteLeftXHi yst out left right)
    (pointAddFiniteLeftXLo yst out left right)

def pointAddDoubleXSqState (yst : EvmState) (out left right : U256) : EvmState :=
  fpMulFinalState (pointAddDoubleXSqArgsState yst out left right)
    (pointAddFiniteLeftXHi yst out left right)
    (pointAddFiniteLeftXLo yst out left right)
    (pointAddFiniteLeftXHi yst out left right)
    (pointAddFiniteLeftXLo yst out left right)

def pointAddDoubleXSqEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00112", "\x00113"].zip
    [(pointAddDoubleXSqResult yst out left right).1,
      (pointAddDoubleXSqResult yst out left right).2] ++
    pointAddYNonzeroEnv yst out left right

theorem step_pointAddDoubleXSq (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddYNonzeroEnv yst out left right)
      (pointAddYSumState yst out left right) pointAddDoubleXSqExpr
      (.vals [(pointAddDoubleXSqResult yst out left right).1,
        (pointAddDoubleXSqResult yst out left right).2]
        (pointAddDoubleXSqState yst out left right)) := by
  rw [pointAddDoubleXSqExpr_eq]
  exact step_fpMul_of_args _ _ _ _
    (step_pointAddDoubleXSqArgs yst out left right) (by rfl)

theorem step_pointAddDoubleXSqStmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddYNonzeroEnv yst out left right)
      (pointAddYSumState yst out left right) pointAddDoubleXSqStmt
      (pointAddDoubleXSqEnv yst out left right)
      (pointAddDoubleXSqState yst out left right) .normal := by
  rw [pointAddDoubleXSqStmt_eq]
  exact Step.letVal (step_pointAddDoubleXSq yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
