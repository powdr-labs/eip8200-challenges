import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYSumCall

set_option warningAsError true

/-! Execution and exact classification of the equal-x vertical-tangent test. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddYSumHi (yst : EvmState) (out left right : U256) : U256 :=
  (pointAddYSumResult yst out left right).1

def pointAddYSumLo (yst : EvmState) (out left right : U256) : U256 :=
  (pointAddYSumResult yst out left right).2

def pointAddYZeroValue (yst : EvmState) (out left right : U256) : U256 :=
  fpZeroValue (pointAddYSumHi yst out left right)
    (pointAddYSumLo yst out left right)

private theorem pointAddYSumEnv_hi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddYSumEnv yst out left right) "\x00110" =
      some (pointAddYSumHi yst out left right) := by
  rfl

private theorem pointAddYSumEnv_lo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddYSumEnv yst out left right) "\x00111" =
      some (pointAddYSumLo yst out left right) := by
  rfl

theorem step_pointAddYZero_of_lookup {funs} (yst : EvmState) (out left right : U256)
    (hlookup : lookupFun funs "\x002" = some (fpZeroDecl, sourceFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      pointAddYZeroCondition
      (.vals [pointAddYZeroValue yst out left right]
        (pointAddYSumState yst out left right)) := by
  have hlo : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      (.var "\x00111")
      (.vals [pointAddYSumLo yst out left right]
        (pointAddYSumState yst out left right)) :=
    Step.var (pointAddYSumEnv_lo yst out left right)
  have hhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      (.var "\x00110")
      (.vals [pointAddYSumHi yst out left right]
        (pointAddYSumState yst out left right)) :=
    Step.var (pointAddYSumEnv_hi yst out left right)
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      [.var "\x00110", .var "\x00111"]
      (.vals [pointAddYSumHi yst out left right,
        pointAddYSumLo yst out left right]
        (pointAddYSumState yst out left right)) :=
    Step.argsCons (Step.argsCons Step.argsNil hlo) hhi
  rw [pointAddYZeroCondition_eq]
  exact step_fpZero_of_args _ _ hargs hlookup

theorem step_pointAddYZero (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      pointAddYZeroCondition
      (.vals [pointAddYZeroValue yst out left right]
        (pointAddYSumState yst out left right)) :=
  step_pointAddYZero_of_lookup yst out left right (by rfl)

theorem pointAddYZeroValue_eq_one_iff (yst : EvmState) (out left right : U256) :
    pointAddYZeroValue yst out left right = 1 ↔
      pointAddYSumHi yst out left right = 0 ∧
        pointAddYSumLo yst out left right = 0 := by
  simp only [pointAddYZeroValue, fpZeroValue]
  by_cases hhi : pointAddYSumHi yst out left right = 0 <;>
    by_cases hlo : pointAddYSumLo yst out left right = 0 <;>
    simp_all [b2w]

theorem pointAddYZeroValue_eq_zero_iff (yst : EvmState) (out left right : U256) :
    pointAddYZeroValue yst out left right = 0 ↔
      pointAddYSumHi yst out left right ≠ 0 ∨
        pointAddYSumLo yst out left right ≠ 0 := by
  simp only [pointAddYZeroValue, fpZeroValue]
  by_cases hhi : pointAddYSumHi yst out left right = 0 <;>
    by_cases hlo : pointAddYSumLo yst out left right = 0 <;>
    simp_all [b2w]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
