import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPrefix
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceMsmPointCalls

set_option warningAsError true

/-! First infinity test and left-infinity identity branch of G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddLeftPointerState (yst : EvmState) (out left right : U256) :
    EvmState :=
  touchMemory (pointAddPrefixState yst out left right) 1952 32

def pointAddLeftPointer (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddPrefixState yst out left right).memory 1952

def pointAddLeftInfinityState (yst : EvmState) (out left right : U256) :
    EvmState :=
  pointZeroReadState (pointAddLeftPointerState yst out left right)
    (pointAddLeftPointer yst out left right)

theorem step_pointAddLeftInfinityCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      pointAddLeftInfinityCondition
    (.vals [pointZeroValue (pointAddLeftPointerState yst out left right)
        (pointAddLeftPointer yst out left right)]
      (pointAddLeftInfinityState yst out left right)) := by
  have hoffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) (.lit (.number 1952))
      (.vals [1952] (pointAddPrefixState yst out left right)) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      (.builtin .mload [.lit (.number 1952)])
      (.vals [pointAddLeftPointer yst out left right]
        (pointAddLeftPointerState yst out left right)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hoffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right)
      [.builtin .mload [.lit (.number 1952)]]
      (.vals [pointAddLeftPointer yst out left right]
        (pointAddLeftPointerState yst out left right)) :=
    Step.argsCons Step.argsNil hload
  rw [pointAddLeftInfinityCondition_eq]
  exact step_pointInfinity_of_args _ hargs (by rfl)

def pointAddLeftCopyArgsState (yst : EvmState) (out left right : U256) :
    EvmState :=
  touchMemory (touchMemory (pointAddLeftInfinityState yst out left right)
    1984 32) 1920 32

def pointAddLeftCopyOut (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (touchMemory (pointAddLeftInfinityState yst out left right)
    1984 32).memory 1920

def pointAddLeftCopyRight (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftInfinityState yst out left right).memory 1984

def pointAddLeftFinalState (yst : EvmState) (out left right : U256) : EvmState :=
  msmCopyPointState (pointAddLeftCopyArgsState yst out left right)
    (pointAddLeftCopyOut yst out left right)
    (pointAddLeftCopyRight yst out left right)

private theorem step_pointAddLeftCopy (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      (.call "\x0027"
        [.builtin .mload [.lit (.number 1920)],
          .builtin .mload [.lit (.number 1984)]])
    (.vals [] (pointAddLeftFinalState yst out left right)) := by
  have hrightOffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) (.lit (.number 1984))
      (.vals [1984] (pointAddLeftInfinityState yst out left right)) := Step.lit
  have hright : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      (.builtin .mload [.lit (.number 1984)])
      (.vals [pointAddLeftCopyRight yst out left right]
        (touchMemory (pointAddLeftInfinityState yst out left right)
          1984 32)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hrightOffset) rfl
  have houtOffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (touchMemory (pointAddLeftInfinityState yst out left right) 1984 32)
      (.lit (.number 1920))
      (.vals [1920] (touchMemory
        (pointAddLeftInfinityState yst out left right) 1984 32)) := Step.lit
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (touchMemory (pointAddLeftInfinityState yst out left right) 1984 32)
      (.builtin .mload [.lit (.number 1920)])
      (.vals [pointAddLeftCopyOut yst out left right]
        (pointAddLeftCopyArgsState yst out left right)) :=
    Step.builtinOk (Step.argsCons Step.argsNil houtOffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      [.builtin .mload [.lit (.number 1920)],
        .builtin .mload [.lit (.number 1984)]]
      (.vals [pointAddLeftCopyOut yst out left right,
          pointAddLeftCopyRight yst out left right]
        (pointAddLeftCopyArgsState yst out left right)) :=
    Step.argsCons (Step.argsCons Step.argsNil hright) hout
  exact step_msmCopyPoint_of_args _ _ hargs (by rfl)

private theorem step_pointAddLeftInfinityBody (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      (.block pointAddLeftInfinityBody) (pointAddInitialEnv out left right)
      (pointAddLeftFinalState yst out left right) .leave := by
  rw [pointAddLeftInfinityBody_eq]
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      [.exprStmt (.call "\x0027"
        [.builtin .mload [.lit (.number 1920)],
          .builtin .mload [.lit (.number 1984)]]), .leave]
      (pointAddInitialEnv out left right)
      (pointAddLeftFinalState yst out left right) .leave :=
    Step.seqCons (Step.exprStmt (step_pointAddLeftCopy yst out left right))
      (Step.seqStop Step.leave (by decide))
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := [.exprStmt (.call "\x0027"
      [.builtin .mload [.lit (.number 1920)],
        .builtin .mload [.lit (.number 1984)]]), .leave]) hbody
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddLeftInfinity (yst : EvmState) (out left right : U256)
    (hinfinity : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) pointAddStmt3
      (pointAddInitialEnv out left right)
      (pointAddLeftFinalState yst out left right) .leave := by
  rw [pointAddStmt3_eq]
  exact Step.ifTrue (step_pointAddLeftInfinityCondition yst out left right) hinfinity
    (step_pointAddLeftInfinityBody yst out left right)

theorem step_pointAddLeftFinite (yst : EvmState) (out left right : U256)
    (hfinite : pointZeroValue (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) pointAddStmt3
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) .normal := by
  rw [pointAddStmt3_eq]
  exact Step.ifFalse (step_pointAddLeftInfinityCondition yst out left right) hfinite

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
