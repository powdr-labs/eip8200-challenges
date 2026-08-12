import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddPrefix

set_option warningAsError true

/-! Relational evaluation of G1MSM `pointAdd`'s first infinity condition. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddLeftPointer (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddPrefixState yst out left right).memory 1568

def pointAddLeftPointerState (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddPrefixState yst out left right) 1568 32

def pointAddLeftInfinityState (yst : EvmState) (out left right : U256) : EvmState :=
  pointInfinityFinalState (pointAddLeftPointerState yst out left right)
    (pointAddLeftPointer yst out left right)

theorem step_pointAddLeftInfinityCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) pointAddLeftInfinityCondition
      (.vals [pointInfinityResult
        (pointAddLeftPointerState yst out left right)
        (pointAddLeftPointer yst out left right)]
        (pointAddLeftInfinityState yst out left right)) := by
  have hoffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) (.lit (.number 1568))
      (.vals [1568] (pointAddPrefixState yst out left right)) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      (.builtin .mload [.lit (.number 1568)])
      (.vals [pointAddLeftPointer yst out left right]
        (pointAddLeftPointerState yst out left right)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hoffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      [.builtin .mload [.lit (.number 1568)]]
      (.vals [pointAddLeftPointer yst out left right]
        (pointAddLeftPointerState yst out left right)) :=
    Step.argsCons Step.argsNil hload
  have hlookup : lookupFun pointAddBodyFuns "\x0015" =
      some (pointInfinityDecl, sourceFuns) := by
    rfl
  rw [pointAddLeftInfinityCondition_eq]
  exact step_pointInfinity_of_args
    (pointAddLeftPointer yst out left right) hargs hlookup

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
