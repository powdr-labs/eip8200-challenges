import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPostDefs

set_option warningAsError true

/-! Arithmetic stages of the common finite G2MSM `pointAdd` postlude. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_literalMul {funs V} (yst : EvmState)
    (out a b : Nat)
    (hlookup : lookupFun funs "\x0016" = some (fp2MulDecl, fp2MulFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.call "\x0016"
        [.lit (.number out), .lit (.number a), .lit (.number b)])
      (.vals [] (fp2MulFinalState yst out a b)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
      [.lit (.number out), .lit (.number a), .lit (.number b)]
      (.vals [out, a, b] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
      Step.lit) Step.lit
  exact step_fp2Mul_of_args _ _ _ hargs hlookup

private theorem step_literalSub {funs V} (yst : EvmState)
    (out a b : Nat)
    (hlookup : lookupFun funs "\x0015" = some (fp2SubDecl, fp2SubFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.call "\x0015"
        [.lit (.number out), .lit (.number a), .lit (.number b)])
      (.vals [] (fp2SubFinalState yst out a b)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
      [.lit (.number out), .lit (.number a), .lit (.number b)]
      (.vals [out, a, b] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
      Step.lit) Step.lit
  exact step_fp2Sub_of_args _ _ _ hargs hlookup

def pointAddPostSquareState (yst : EvmState) : EvmState :=
  fp2MulFinalState yst 2688 2048 2048

private theorem pointAddStmt7_eq : pointAddStmt7 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2688), .lit (.number 2048), .lit (.number 2048)]) := by rfl

theorem step_pointAddPostSquare (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt7
      (pointAddInitialEnv out left right) (pointAddPostSquareState yst)
      .normal := by
  rw [pointAddStmt7_eq]
  exact Step.exprStmt (step_literalMul yst 2688 2048 2048 (by rfl))

def pointAddPostLeftReadState (yst : EvmState) : EvmState :=
  touchMemory yst 1952 32

def pointAddPostLeft (yst : EvmState) : U256 := loadWord yst.memory 1952

def pointAddPostSubLeftState (yst : EvmState) : EvmState :=
  fp2SubFinalState (pointAddPostLeftReadState yst) 2688 2688
    (pointAddPostLeft yst)

private theorem pointAddStmt8_eq : pointAddStmt8 =
    .exprStmt (.call "\x0015"
      [.lit (.number 2688), .lit (.number 2688),
        .builtin .mload [.lit (.number 1952)]]) := by rfl

theorem step_pointAddPostSubLeft (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt8
      (pointAddInitialEnv out left right) (pointAddPostSubLeftState yst)
      .normal := by
  rw [pointAddStmt8_eq]
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      (.builtin .mload [.lit (.number 1952)])
      (.vals [pointAddPostLeft yst] (pointAddPostLeftReadState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl
  have ha : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddPostLeftReadState yst)
      (.lit (.number 2688))
      (.vals [2688] (pointAddPostLeftReadState yst)) := Step.lit
  have hout := ha
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      [.lit (.number 2688), .lit (.number 2688),
        .builtin .mload [.lit (.number 1952)]]
      (.vals [2688, 2688, pointAddPostLeft yst]
        (pointAddPostLeftReadState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hload) ha) hout
  exact Step.exprStmt (step_fp2Sub_of_args _ _ _ hargs (by rfl))

def pointAddPostRightReadState (yst : EvmState) : EvmState :=
  touchMemory yst 1984 32

def pointAddPostRight (yst : EvmState) : U256 := loadWord yst.memory 1984

def pointAddPostSubRightState (yst : EvmState) : EvmState :=
  fp2SubFinalState (pointAddPostRightReadState yst) 2688 2688
    (pointAddPostRight yst)

private theorem pointAddStmt9_eq : pointAddStmt9 =
    .exprStmt (.call "\x0015"
      [.lit (.number 2688), .lit (.number 2688),
        .builtin .mload [.lit (.number 1984)]]) := by rfl

theorem step_pointAddPostSubRight (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt9
      (pointAddInitialEnv out left right) (pointAddPostSubRightState yst)
      .normal := by
  rw [pointAddStmt9_eq]
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      (.builtin .mload [.lit (.number 1984)])
      (.vals [pointAddPostRight yst] (pointAddPostRightReadState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl
  have ha : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddPostRightReadState yst)
      (.lit (.number 2688))
      (.vals [2688] (pointAddPostRightReadState yst)) := Step.lit
  have hout := ha
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      [.lit (.number 2688), .lit (.number 2688),
        .builtin .mload [.lit (.number 1984)]]
      (.vals [2688, 2688, pointAddPostRight yst]
        (pointAddPostRightReadState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hload) ha) hout
  exact Step.exprStmt (step_fp2Sub_of_args _ _ _ hargs (by rfl))

def pointAddPostDeltaXReadState (yst : EvmState) : EvmState :=
  touchMemory yst 1952 32

def pointAddPostDeltaXLeft (yst : EvmState) : U256 := loadWord yst.memory 1952

def pointAddPostDeltaXState (yst : EvmState) : EvmState :=
  fp2SubFinalState (pointAddPostDeltaXReadState yst) 2816
    (pointAddPostDeltaXLeft yst) 2688

private theorem pointAddStmt10_eq : pointAddStmt10 =
    .exprStmt (.call "\x0015"
      [.lit (.number 2816),
        .builtin .mload [.lit (.number 1952)],
        .lit (.number 2688)]) := by rfl

theorem step_pointAddPostDeltaX (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt10
      (pointAddInitialEnv out left right) (pointAddPostDeltaXState yst)
      .normal := by
  rw [pointAddStmt10_eq]
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      (.builtin .mload [.lit (.number 1952)])
      (.vals [pointAddPostDeltaXLeft yst]
        (pointAddPostDeltaXReadState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl
  have hb : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst (.lit (.number 2688))
      (.vals [2688] yst) := Step.lit
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddPostDeltaXReadState yst)
      (.lit (.number 2816))
      (.vals [2816] (pointAddPostDeltaXReadState yst)) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      [.lit (.number 2816),
        .builtin .mload [.lit (.number 1952)],
        .lit (.number 2688)]
      (.vals [2816, pointAddPostDeltaXLeft yst, 2688]
        (pointAddPostDeltaXReadState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hb) hload) hout
  exact Step.exprStmt (step_fp2Sub_of_args _ _ _ hargs (by rfl))

def pointAddPostMulYState (yst : EvmState) : EvmState :=
  fp2MulFinalState yst 2944 2048 2816

private theorem pointAddStmt11_eq : pointAddStmt11 =
    .exprStmt (.call "\x0016"
      [.lit (.number 2944), .lit (.number 2048), .lit (.number 2816)]) := by rfl

theorem step_pointAddPostMulY (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt11
      (pointAddInitialEnv out left right) (pointAddPostMulYState yst)
      .normal := by
  rw [pointAddStmt11_eq]
  exact Step.exprStmt (step_literalMul yst 2944 2048 2816 (by rfl))

def pointAddPostLeftYReadState (yst : EvmState) : EvmState :=
  touchMemory yst 1952 32

def pointAddPostLeftY (yst : EvmState) : U256 := loadWord yst.memory 1952 + 128

def pointAddPostSubYState (yst : EvmState) : EvmState :=
  fp2SubFinalState (pointAddPostLeftYReadState yst) 2944 2944
    (pointAddPostLeftY yst)

private theorem pointAddStmt12_eq : pointAddStmt12 =
    .exprStmt (.call "\x0015"
      [.lit (.number 2944), .lit (.number 2944),
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)]]) := by rfl

theorem step_pointAddPostSubY (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt12
      (pointAddInitialEnv out left right) (pointAddPostSubYState yst)
      .normal := by
  rw [pointAddStmt12_eq]
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      (.builtin .mload [.lit (.number 1952)])
      (.vals [loadWord yst.memory 1952] (pointAddPostLeftYReadState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst (.lit (.number 128))
      (.vals [128] yst) := Step.lit
  have hadd : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      (.builtin .add
        [.builtin .mload [.lit (.number 1952)], .lit (.number 128)])
      (.vals [pointAddPostLeftY yst] (pointAddPostLeftYReadState yst)) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hlit) hload) rfl
  have ha : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddPostLeftYReadState yst)
      (.lit (.number 2944))
      (.vals [2944] (pointAddPostLeftYReadState yst)) := Step.lit
  have hout := ha
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      [.lit (.number 2944), .lit (.number 2944),
        .builtin .add
          [.builtin .mload [.lit (.number 1952)], .lit (.number 128)]]
      (.vals [2944, 2944, pointAddPostLeftY yst]
        (pointAddPostLeftYReadState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hadd) ha) hout
  exact Step.exprStmt (step_fp2Sub_of_args _ _ _ hargs (by rfl))

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
