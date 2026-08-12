import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDoubleBranch

set_option warningAsError true

/-! Arithmetic stages producing the slope in the G2MSM unequal branch. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_mload1952 (yst : EvmState) {funs V} :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload [.lit (.number 1952)])
      (.vals [loadWord yst.memory 1952] (touchMemory yst 1952 32)) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl

private theorem step_mload1984 (yst : EvmState) {funs V} :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload [.lit (.number 1984)])
      (.vals [loadWord yst.memory 1984] (touchMemory yst 1984 32)) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl

private theorem step_addMload1952 (yst : EvmState) {funs V} :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .add
        [.builtin .mload [.lit (.number 1952)], .lit (.number 128)])
      (.vals [loadWord yst.memory 1952 + 128]
        (touchMemory yst 1952 32)) := by
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.lit (.number 128)) (.vals [128] yst) := Step.lit
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil hlit)
      (step_mload1952 yst)) rfl

private theorem step_addMload1984 (yst : EvmState) {funs V} :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .add
        [.builtin .mload [.lit (.number 1984)], .lit (.number 128)])
      (.vals [loadWord yst.memory 1984 + 128]
        (touchMemory yst 1984 32)) := by
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.lit (.number 128)) (.vals [128] yst) := Step.lit
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil hlit)
      (step_mload1984 yst)) rfl

def pointAddUnequalYLeftRead (yst : EvmState) : EvmState :=
  touchMemory yst 1952 32

def pointAddUnequalYLeft (yst : EvmState) : U256 :=
  loadWord yst.memory 1952 + 128

def pointAddUnequalYArgsState (yst : EvmState) : EvmState :=
  touchMemory (pointAddUnequalYLeftRead yst) 1984 32

def pointAddUnequalYRight (yst : EvmState) : U256 :=
  loadWord (pointAddUnequalYLeftRead yst).memory 1984 + 128

def pointAddUnequalYState (yst : EvmState) : EvmState :=
  fp2SubFinalState (pointAddUnequalYArgsState yst) 2304
    (pointAddUnequalYRight yst) (pointAddUnequalYLeft yst)

private theorem pointAddUnequalStmt0_eq : pointAddUnequalStmt0 =
    .exprStmt (.call "\x0015"
      [.lit (.number 2304),
        .builtin .add
          [.builtin .mload [.lit (.number 1984)], .lit (.number 128)],
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)]]) := by rfl

theorem step_pointAddUnequalYDiff (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddUnequalStmt0 (pointAddInitialEnv out left right)
      (pointAddUnequalYState yst) .normal := by
  rw [pointAddUnequalStmt0_eq]
  have hleft := step_addMload1952 yst (funs := [] :: pointAddBodyFuns)
    (V := pointAddInitialEnv out left right)
  have hright := step_addMload1984 (pointAddUnequalYLeftRead yst)
    (funs := [] :: pointAddBodyFuns) (V := pointAddInitialEnv out left right)
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddUnequalYArgsState yst) (.lit (.number 2304))
      (.vals [2304] (pointAddUnequalYArgsState yst)) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2304),
        .builtin .add
          [.builtin .mload [.lit (.number 1984)], .lit (.number 128)],
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)]]
      (.vals [2304, pointAddUnequalYRight yst, pointAddUnequalYLeft yst]
        (pointAddUnequalYArgsState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hleft) hright) hout
  exact Step.exprStmt (step_fp2Sub_of_args _ _ _ hargs (by rfl))

def pointAddUnequalXLeftRead (yst : EvmState) : EvmState :=
  touchMemory yst 1952 32

def pointAddUnequalXLeft (yst : EvmState) : U256 :=
  loadWord yst.memory 1952

def pointAddUnequalXArgsState (yst : EvmState) : EvmState :=
  touchMemory (pointAddUnequalXLeftRead yst) 1984 32

def pointAddUnequalXRight (yst : EvmState) : U256 :=
  loadWord (pointAddUnequalXLeftRead yst).memory 1984

def pointAddUnequalXState (yst : EvmState) : EvmState :=
  fp2SubFinalState (pointAddUnequalXArgsState yst) 2432
    (pointAddUnequalXRight yst) (pointAddUnequalXLeft yst)

private theorem pointAddUnequalStmt1_eq : pointAddUnequalStmt1 =
    .exprStmt (.call "\x0015"
      [.lit (.number 2432),
        .builtin .mload [.lit (.number 1984)],
        .builtin .mload [.lit (.number 1952)]]) := by rfl

theorem step_pointAddUnequalXDiff (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddUnequalStmt1 (pointAddInitialEnv out left right)
      (pointAddUnequalXState yst) .normal := by
  rw [pointAddUnequalStmt1_eq]
  have hleft := step_mload1952 yst (funs := [] :: pointAddBodyFuns)
    (V := pointAddInitialEnv out left right)
  have hright := step_mload1984 (pointAddUnequalXLeftRead yst)
    (funs := [] :: pointAddBodyFuns) (V := pointAddInitialEnv out left right)
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddUnequalXArgsState yst) (.lit (.number 2432))
      (.vals [2432] (pointAddUnequalXArgsState yst)) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2432),
        .builtin .mload [.lit (.number 1984)],
        .builtin .mload [.lit (.number 1952)]]
      (.vals [2432, pointAddUnequalXRight yst, pointAddUnequalXLeft yst]
        (pointAddUnequalXArgsState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hleft) hright) hout
  exact Step.exprStmt (step_fp2Sub_of_args _ _ _ hargs (by rfl))

def pointAddUnequalInvState (yst : EvmState) : EvmState :=
  fp2InvFinalState yst 2560 2432

private theorem pointAddUnequalStmt2_eq : pointAddUnequalStmt2 =
    .exprStmt (.call "\x0017"
      [.lit (.number 2560), .lit (.number 2432)]) := by rfl

theorem step_pointAddUnequalInverse (yst : EvmState) (out left right : U256)
    (hhi : (fp2InvNorm yst 2432).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddUnequalStmt2 (pointAddInitialEnv out left right)
      (pointAddUnequalInvState yst) .normal := by
  rw [pointAddUnequalStmt2_eq]
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2560), .lit (.number 2432)]
      (.vals [2560, 2432] yst) :=
    Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  exact Step.exprStmt (step_fp2Inv_of_args _ _ hargs (by rfl) hhi)

def pointAddUnequalSlopeState (yst : EvmState) : EvmState :=
  fp2MulFinalState yst 2048 2304 2560

private theorem pointAddUnequalStmt3_eq : pointAddUnequalStmt3 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2048), .lit (.number 2304), .lit (.number 2560)]) := by rfl

theorem step_pointAddUnequalSlope (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddUnequalStmt3 (pointAddInitialEnv out left right)
      (pointAddUnequalSlopeState yst) .normal := by
  rw [pointAddUnequalStmt3_eq]
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2048), .lit (.number 2304), .lit (.number 2560)]
      (.vals [2048, 2304, 2560] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
      Step.lit) Step.lit
  exact Step.exprStmt (step_fp2Mul_of_args _ _ _ hargs (by rfl))

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
