import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDoubleYSum

set_option warningAsError true

/-! Arithmetic stages producing the slope in the G2MSM double branch. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_mload1952 (yst : EvmState) {funs V} :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload [.lit (.number 1952)])
      (.vals [loadWord yst.memory 1952] (touchMemory yst 1952 32)) :=
  Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl

private theorem step_literalCall3 {funs V} (yst : EvmState)
    (out a b : Nat)
    (hlookup : lookupFun funs "\x0014" = some (fp2AddDecl, fp2AddFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.call "\x0014" [.lit (.number out), .lit (.number a), .lit (.number b)])
      (.vals [] (fp2AddFinalState yst out a b)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
      [.lit (.number out), .lit (.number a), .lit (.number b)]
      (.vals [out, a, b] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
      Step.lit) Step.lit
  exact step_fp2Add_of_args _ _ _ hargs hlookup

def pointAddDoubleSquareRead1 (yst : EvmState) : EvmState :=
  touchMemory yst 1952 32

def pointAddDoubleSquareX1 (yst : EvmState) : U256 :=
  loadWord yst.memory 1952

def pointAddDoubleSquareRead2 (yst : EvmState) : EvmState :=
  touchMemory (pointAddDoubleSquareRead1 yst) 1952 32

def pointAddDoubleSquareX2 (yst : EvmState) : U256 :=
  loadWord (pointAddDoubleSquareRead1 yst).memory 1952

def pointAddDoubleSquareState (yst : EvmState) : EvmState :=
  fp2MulFinalState (pointAddDoubleSquareRead2 yst) 2176
    (pointAddDoubleSquareX2 yst) (pointAddDoubleSquareX1 yst)

private theorem pointAddEqualStmt2_eq : pointAddEqualStmt2 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2176),
        .builtin .mload [.lit (.number 1952)],
        .builtin .mload [.lit (.number 1952)]]) := by rfl

theorem step_pointAddDoubleSquare (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt2 (pointAddInitialEnv out left right)
      (pointAddDoubleSquareState yst) .normal := by
  rw [pointAddEqualStmt2_eq]
  have hx1 := step_mload1952 yst (funs := [] :: pointAddBodyFuns)
    (V := pointAddInitialEnv out left right)
  have hx2 := step_mload1952 (pointAddDoubleSquareRead1 yst)
    (funs := [] :: pointAddBodyFuns)
    (V := pointAddInitialEnv out left right)
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddDoubleSquareRead2 yst) (.lit (.number 2176))
      (.vals [2176] (pointAddDoubleSquareRead2 yst)) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2176),
        .builtin .mload [.lit (.number 1952)],
        .builtin .mload [.lit (.number 1952)]]
      (.vals [2176, pointAddDoubleSquareX2 yst,
          pointAddDoubleSquareX1 yst]
        (pointAddDoubleSquareRead2 yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hx1) hx2) hout
  exact Step.exprStmt (step_fp2Mul_of_args _ _ _ hargs (by rfl))

def pointAddDoubleNum2State (yst : EvmState) : EvmState :=
  fp2AddFinalState yst 2304 2176 2176

private theorem pointAddEqualStmt3_eq : pointAddEqualStmt3 =
    .exprStmt (.call "\x0014"
      [.lit (.number 2304), .lit (.number 2176), .lit (.number 2176)]) := by rfl

theorem step_pointAddDoubleNum2 (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt3 (pointAddInitialEnv out left right)
      (pointAddDoubleNum2State yst) .normal := by
  rw [pointAddEqualStmt3_eq]
  exact Step.exprStmt (step_literalCall3 yst 2304 2176 2176 (by rfl))

def pointAddDoubleNum3State (yst : EvmState) : EvmState :=
  fp2AddFinalState yst 2304 2304 2176

private theorem pointAddEqualStmt4_eq : pointAddEqualStmt4 =
    .exprStmt (.call "\x0014"
      [.lit (.number 2304), .lit (.number 2304), .lit (.number 2176)]) := by rfl

theorem step_pointAddDoubleNum3 (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt4 (pointAddInitialEnv out left right)
      (pointAddDoubleNum3State yst) .normal := by
  rw [pointAddEqualStmt4_eq]
  exact Step.exprStmt (step_literalCall3 yst 2304 2304 2176 (by rfl))

def pointAddDoubleDenRead1 (yst : EvmState) : EvmState :=
  touchMemory yst 1952 32

def pointAddDoubleDenY1 (yst : EvmState) : U256 :=
  loadWord yst.memory 1952 + 128

def pointAddDoubleDenRead2 (yst : EvmState) : EvmState :=
  touchMemory (pointAddDoubleDenRead1 yst) 1952 32

def pointAddDoubleDenY2 (yst : EvmState) : U256 :=
  loadWord (pointAddDoubleDenRead1 yst).memory 1952 + 128

def pointAddDoubleDenState (yst : EvmState) : EvmState :=
  fp2AddFinalState (pointAddDoubleDenRead2 yst) 2432
    (pointAddDoubleDenY2 yst) (pointAddDoubleDenY1 yst)

private theorem pointAddEqualStmt5_eq : pointAddEqualStmt5 =
    .exprStmt (.call "\x0014"
      [.lit (.number 2432),
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)],
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)]]) := by rfl

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

theorem step_pointAddDoubleDenominator (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt5 (pointAddInitialEnv out left right)
      (pointAddDoubleDenState yst) .normal := by
  rw [pointAddEqualStmt5_eq]
  have hy1 := step_addMload1952 yst (funs := [] :: pointAddBodyFuns)
    (V := pointAddInitialEnv out left right)
  have hy2 := step_addMload1952 (pointAddDoubleDenRead1 yst)
    (funs := [] :: pointAddBodyFuns) (V := pointAddInitialEnv out left right)
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddDoubleDenRead2 yst) (.lit (.number 2432))
      (.vals [2432] (pointAddDoubleDenRead2 yst)) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2432),
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)],
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)]]
      (.vals [2432, pointAddDoubleDenY2 yst, pointAddDoubleDenY1 yst]
        (pointAddDoubleDenRead2 yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hy1) hy2) hout
  exact Step.exprStmt (step_fp2Add_of_args _ _ _ hargs (by rfl))

def pointAddDoubleInvState (yst : EvmState) : EvmState :=
  fp2InvFinalState yst 2560 2432

private theorem pointAddEqualStmt6_eq : pointAddEqualStmt6 =
    .exprStmt (.call "\x0017"
      [.lit (.number 2560), .lit (.number 2432)]) := by rfl

theorem step_pointAddDoubleInverse (yst : EvmState) (out left right : U256)
    (hhi : (fp2InvNorm yst 2432).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt6 (pointAddInitialEnv out left right)
      (pointAddDoubleInvState yst) .normal := by
  rw [pointAddEqualStmt6_eq]
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2560), .lit (.number 2432)]
      (.vals [2560, 2432] yst) :=
    Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  exact Step.exprStmt (step_fp2Inv_of_args _ _ hargs (by rfl) hhi)

def pointAddDoubleSlopeState (yst : EvmState) : EvmState :=
  fp2MulFinalState yst 2048 2304 2560

private theorem pointAddEqualStmt7_eq : pointAddEqualStmt7 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2048), .lit (.number 2304),
        .lit (.number 2560)]) := by rfl

theorem step_pointAddDoubleSlope (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt7 (pointAddInitialEnv out left right)
      (pointAddDoubleSlopeState yst) .normal := by
  rw [pointAddEqualStmt7_eq]
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      [.lit (.number 2048), .lit (.number 2304), .lit (.number 2560)]
      (.vals [2048, 2304, 2560] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
      Step.lit) Step.lit
  exact Step.exprStmt (step_fp2Mul_of_args _ _ _ hargs (by rfl))

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
