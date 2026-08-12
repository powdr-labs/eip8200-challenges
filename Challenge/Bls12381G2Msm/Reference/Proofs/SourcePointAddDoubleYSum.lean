import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddFiniteCondition
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2Calls

set_option warningAsError true

/-! Y-coordinate sum and nonzero fallthrough of the G2MSM double branch. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYRightReadState (yst : EvmState) : EvmState :=
  touchMemory yst 1984 32

def pointAddDoubleYRight (yst : EvmState) : U256 :=
  loadWord yst.memory 1984 + 128

def pointAddDoubleYArgsState (yst : EvmState) : EvmState :=
  touchMemory (pointAddDoubleYRightReadState yst) 1952 32

def pointAddDoubleYLeft (yst : EvmState) : U256 :=
  loadWord (pointAddDoubleYRightReadState yst).memory 1952 + 128

def pointAddDoubleYSumState (yst : EvmState) : EvmState :=
  fp2AddFinalState (pointAddDoubleYArgsState yst) 2048
    (pointAddDoubleYLeft yst) (pointAddDoubleYRight yst)

private theorem pointAddEqualStmt0_eq : pointAddEqualStmt0 =
    .exprStmt (.call "\x0014"
      [.lit (.number 2048),
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)],
        .builtin .add
          [.builtin .mload [.lit (.number 1984)], .lit (.number 128)]]) := by rfl

private theorem step_addMload1984 (yst : EvmState) {funs V} :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .add
        [.builtin .mload [.lit (.number 1984)], .lit (.number 128)])
      (.vals [pointAddDoubleYRight yst]
        (pointAddDoubleYRightReadState yst)) := by
  have hoffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.lit (.number 1984)) (.vals [1984] yst) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload [.lit (.number 1984)])
      (.vals [loadWord yst.memory 1984]
        (pointAddDoubleYRightReadState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hoffset) rfl
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      yst (.lit (.number 128)) (.vals [128] yst) := Step.lit
  exact Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hlit) hload) rfl

private theorem step_addMload1952 (yst : EvmState) {funs V} :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleYRightReadState yst)
      (.builtin .add
        [.builtin .mload [.lit (.number 1952)], .lit (.number 128)])
      (.vals [pointAddDoubleYLeft yst] (pointAddDoubleYArgsState yst)) := by
  have hoffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleYRightReadState yst) (.lit (.number 1952))
      (.vals [1952] (pointAddDoubleYRightReadState yst)) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleYRightReadState yst)
      (.builtin .mload [.lit (.number 1952)])
      (.vals [loadWord (pointAddDoubleYRightReadState yst).memory 1952]
        (pointAddDoubleYArgsState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hoffset) rfl
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleYRightReadState yst) (.lit (.number 128))
      (.vals [128] (pointAddDoubleYRightReadState yst)) := Step.lit
  exact Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hlit) hload) rfl

theorem step_pointAddDoubleYSum (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt0 (pointAddInitialEnv out left right)
      (pointAddDoubleYSumState yst) .normal := by
  rw [pointAddEqualStmt0_eq]
  have hright := step_addMload1984 yst
    (funs := [] :: pointAddBodyFuns) (V := pointAddInitialEnv out left right)
  have hleft := step_addMload1952 yst
    (funs := [] :: pointAddBodyFuns) (V := pointAddInitialEnv out left right)
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddDoubleYArgsState yst) (.lit (.number 2048))
      (.vals [2048] (pointAddDoubleYArgsState yst)) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2048),
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)],
        .builtin .add
          [.builtin .mload [.lit (.number 1984)], .lit (.number 128)]]
      (.vals [2048, pointAddDoubleYLeft yst, pointAddDoubleYRight yst]
        (pointAddDoubleYArgsState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hright) hleft) hout
  exact Step.exprStmt (step_fp2Add_of_args _ _ _ hargs (by rfl))

def pointAddDoubleYZero (yst : EvmState) : U256 :=
  fp2ZeroValue yst 2048

def pointAddAfterDoubleYZero (yst : EvmState) : EvmState :=
  fp2ReadState yst 2048

theorem step_pointAddDoubleYZeroCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualYZeroCondition
      (.vals [pointAddDoubleYZero yst] (pointAddAfterDoubleYZero yst)) := by
  rw [pointAddEqualYZeroCondition_eq]
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2048)] (.vals [2048] yst) :=
    Step.argsCons Step.argsNil Step.lit
  exact step_fp2Zero_of_args _ hargs (by rfl)

theorem step_pointAddDoubleYNonzero (yst : EvmState)
    (out left right : U256) (hy : pointAddDoubleYZero yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt1 (pointAddInitialEnv out left right)
      (pointAddAfterDoubleYZero yst) .normal := by
  rw [pointAddEqualYZeroStmt_eq]
  exact Step.ifFalse (step_pointAddDoubleYZeroCondition yst out left right) hy

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
