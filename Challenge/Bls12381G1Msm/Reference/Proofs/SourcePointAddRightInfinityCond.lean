import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddLeftInfinity

set_option warningAsError true

/-! Relational evaluation of G1MSM `pointAdd`'s second infinity condition. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddRightPointer (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftInfinityState yst out left right).memory 1600

def pointAddRightPointerState (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddLeftInfinityState yst out left right) 1600 32

def pointAddRightInfinityState (yst : EvmState) (out left right : U256) : EvmState :=
  pointInfinityFinalState (pointAddRightPointerState yst out left right)
    (pointAddRightPointer yst out left right)

theorem step_pointAddRightInfinityCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      pointAddRightInfinityCondition
      (.vals [pointInfinityResult
        (pointAddRightPointerState yst out left right)
        (pointAddRightPointer yst out left right)]
        (pointAddRightInfinityState yst out left right)) := by
  have hoffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) (.lit (.number 1600))
      (.vals [1600] (pointAddLeftInfinityState yst out left right)) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      (.builtin .mload [.lit (.number 1600)])
      (.vals [pointAddRightPointer yst out left right]
        (pointAddRightPointerState yst out left right)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hoffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      [.builtin .mload [.lit (.number 1600)]]
      (.vals [pointAddRightPointer yst out left right]
        (pointAddRightPointerState yst out left right)) :=
    Step.argsCons Step.argsNil hload
  have hlookup : lookupFun pointAddBodyFuns "\x0015" =
      some (pointInfinityDecl, sourceFuns) := by
    rfl
  rw [pointAddRightInfinityCondition_eq]
  exact step_pointInfinity_of_args
    (pointAddRightPointer yst out left right) hargs hlookup

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
