import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddFiniteDefs
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2PredicateCalls

set_option warningAsError true

/-! Exact equality tests selecting the finite G2MSM `pointAdd` branches. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddEqRightPointerState (yst : EvmState) : EvmState :=
  touchMemory yst 1984 32

def pointAddEqRightPointer (yst : EvmState) : U256 :=
  loadWord yst.memory 1984

def pointAddEqArgsState (yst : EvmState) : EvmState :=
  touchMemory (pointAddEqRightPointerState yst) 1952 32

def pointAddEqLeftPointer (yst : EvmState) : U256 :=
  loadWord (pointAddEqRightPointerState yst).memory 1952

def pointAddEqValue (yst : EvmState) : U256 :=
  fp2EqValue (pointAddEqArgsState yst)
    (pointAddEqLeftPointer yst) (pointAddEqRightPointer yst)

def pointAddEqFinalState (yst : EvmState) : EvmState :=
  fp2EqReadState (pointAddEqArgsState yst)
    (pointAddEqLeftPointer yst) (pointAddEqRightPointer yst)

private theorem step_pointAddEqCall (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      (.call "\x0013"
        [.builtin .mload [.lit (.number 1952)],
          .builtin .mload [.lit (.number 1984)]])
      (.vals [pointAddEqValue yst] (pointAddEqFinalState yst)) := by
  have hrightOffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      (.lit (.number 1984)) (.vals [1984] yst) := Step.lit
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      (.builtin .mload [.lit (.number 1984)])
      (.vals [pointAddEqRightPointer yst]
        (pointAddEqRightPointerState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hrightOffset) rfl
  have hleftOffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddEqRightPointerState yst) (.lit (.number 1952))
      (.vals [1952] (pointAddEqRightPointerState yst)) := Step.lit
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddEqRightPointerState yst)
      (.builtin .mload [.lit (.number 1952)])
      (.vals [pointAddEqLeftPointer yst] (pointAddEqArgsState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hleftOffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      [.builtin .mload [.lit (.number 1952)],
        .builtin .mload [.lit (.number 1984)]]
      (.vals [pointAddEqLeftPointer yst, pointAddEqRightPointer yst]
        (pointAddEqArgsState yst)) :=
    Step.argsCons (Step.argsCons Step.argsNil hright) hleft
  exact step_fp2Eq_of_args _ _ hargs (by rfl)

theorem step_pointAddEqualCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddEqualCondition
      (.vals [pointAddEqValue yst] (pointAddEqFinalState yst)) := by
  rw [pointAddEqualCondition_eq]
  exact step_pointAddEqCall yst out left right

theorem step_pointAddUnequalCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddUnequalCondition
      (.vals [b2w (pointAddEqValue yst = 0)]
        (pointAddEqFinalState yst)) := by
  rw [pointAddUnequalCondition_eq]
  exact Step.builtinOk
    (Step.argsCons Step.argsNil (step_pointAddEqCall yst out left right)) rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
