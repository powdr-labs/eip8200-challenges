import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddLeftIdentity

set_option warningAsError true

/-! Second infinity test and right-infinity identity branch of G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddRightPointerState (yst : EvmState) (out left right : U256) :
    EvmState :=
  touchMemory (pointAddLeftInfinityState yst out left right) 1984 32

def pointAddRightPointer (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftInfinityState yst out left right).memory 1984

def pointAddRightInfinityState (yst : EvmState) (out left right : U256) :
    EvmState :=
  pointZeroReadState (pointAddRightPointerState yst out left right)
    (pointAddRightPointer yst out left right)

theorem step_pointAddRightInfinityCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      pointAddRightInfinityCondition
      (.vals [pointZeroValue (pointAddRightPointerState yst out left right)
          (pointAddRightPointer yst out left right)]
        (pointAddRightInfinityState yst out left right)) := by
  have hoffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) (.lit (.number 1984))
      (.vals [1984] (pointAddLeftInfinityState yst out left right)) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      (.builtin .mload [.lit (.number 1984)])
      (.vals [pointAddRightPointer yst out left right]
        (pointAddRightPointerState yst out left right)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hoffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      [.builtin .mload [.lit (.number 1984)]]
      (.vals [pointAddRightPointer yst out left right]
        (pointAddRightPointerState yst out left right)) :=
    Step.argsCons Step.argsNil hload
  rw [pointAddRightInfinityCondition_eq]
  exact step_pointInfinity_of_args _ hargs (by rfl)

def pointAddRightCopyArgsState (yst : EvmState) (out left right : U256) :
    EvmState :=
  touchMemory (touchMemory (pointAddRightInfinityState yst out left right)
    1952 32) 1920 32

def pointAddRightCopyOut (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (touchMemory (pointAddRightInfinityState yst out left right)
    1952 32).memory 1920

def pointAddRightCopyLeft (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddRightInfinityState yst out left right).memory 1952

def pointAddRightFinalState (yst : EvmState) (out left right : U256) : EvmState :=
  msmCopyPointState (pointAddRightCopyArgsState yst out left right)
    (pointAddRightCopyOut yst out left right)
    (pointAddRightCopyLeft yst out left right)

private theorem step_pointAddRightCopy (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right)
      (.call "\x0027"
        [.builtin .mload [.lit (.number 1920)],
          .builtin .mload [.lit (.number 1952)]])
      (.vals [] (pointAddRightFinalState yst out left right)) := by
  have hleftOffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right) (.lit (.number 1952))
      (.vals [1952] (pointAddRightInfinityState yst out left right)) := Step.lit
  have hleft : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right)
      (.builtin .mload [.lit (.number 1952)])
      (.vals [pointAddRightCopyLeft yst out left right]
        (touchMemory (pointAddRightInfinityState yst out left right)
          1952 32)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hleftOffset) rfl
  have houtOffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (touchMemory (pointAddRightInfinityState yst out left right) 1952 32)
      (.lit (.number 1920))
      (.vals [1920] (touchMemory
        (pointAddRightInfinityState yst out left right) 1952 32)) := Step.lit
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (touchMemory (pointAddRightInfinityState yst out left right) 1952 32)
      (.builtin .mload [.lit (.number 1920)])
      (.vals [pointAddRightCopyOut yst out left right]
        (pointAddRightCopyArgsState yst out left right)) :=
    Step.builtinOk (Step.argsCons Step.argsNil houtOffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right)
      [.builtin .mload [.lit (.number 1920)],
        .builtin .mload [.lit (.number 1952)]]
      (.vals [pointAddRightCopyOut yst out left right,
          pointAddRightCopyLeft yst out left right]
        (pointAddRightCopyArgsState yst out left right)) :=
    Step.argsCons (Step.argsCons Step.argsNil hleft) hout
  exact step_msmCopyPoint_of_args _ _ hargs (by rfl)

private theorem step_pointAddRightInfinityBody (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right)
      (.block pointAddRightInfinityBody) (pointAddInitialEnv out left right)
      (pointAddRightFinalState yst out left right) .leave := by
  rw [pointAddRightInfinityBody_eq]
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right)
      [.exprStmt (.call "\x0027"
        [.builtin .mload [.lit (.number 1920)],
          .builtin .mload [.lit (.number 1952)]]), .leave]
      (pointAddInitialEnv out left right)
      (pointAddRightFinalState yst out left right) .leave :=
    Step.seqCons (Step.exprStmt (step_pointAddRightCopy yst out left right))
      (Step.seqStop Step.leave (by decide))
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := [.exprStmt (.call "\x0027"
      [.builtin .mload [.lit (.number 1920)],
        .builtin .mload [.lit (.number 1952)]]), .leave]) hbody
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddRightInfinity (yst : EvmState) (out left right : U256)
    (hinfinity : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) pointAddStmt4
      (pointAddInitialEnv out left right)
      (pointAddRightFinalState yst out left right) .leave := by
  rw [pointAddStmt4_eq]
  exact Step.ifTrue (step_pointAddRightInfinityCondition yst out left right)
    hinfinity (step_pointAddRightInfinityBody yst out left right)

theorem step_pointAddRightFinite (yst : EvmState) (out left right : U256)
    (hfinite : pointZeroValue (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) pointAddStmt4
      (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right) .normal := by
  rw [pointAddStmt4_eq]
  exact Step.ifFalse (step_pointAddRightInfinityCondition yst out left right)
    hfinite

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
