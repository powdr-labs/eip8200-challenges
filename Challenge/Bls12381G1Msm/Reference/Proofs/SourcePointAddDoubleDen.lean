import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleNum3

set_option warningAsError true

/-! Staged post-multiplication Y loads for the point-doubling denominator. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleLeftPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddDoubleXSqState yst out left right).memory 1568

def pointAddDoubleLeftYHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddDoubleXSqState yst out left right).memory
    (pointAddDoubleLeftPtr yst out left right + 64).toNat

def pointAddDoubleLeftYLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddDoubleXSqState yst out left right).memory
    (pointAddDoubleLeftPtr yst out left right + 96).toNat

def pointAddDoubleDenState1 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState yst out left right) 1568 32

def pointAddDoubleDenState2 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleDenState1 yst out left right)
    (pointAddDoubleLeftPtr yst out left right + 96).toNat 32

def pointAddDoubleDenState3 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleDenState2 yst out left right) 1568 32

def pointAddDoubleDenState4 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleDenState3 yst out left right)
    (pointAddDoubleLeftPtr yst out left right + 64).toNat 32

def pointAddDoubleDenState5 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleDenState4 yst out left right) 1568 32

def pointAddDoubleDenState6 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleDenState5 yst out left right)
    (pointAddDoubleLeftPtr yst out left right + 96).toNat 32

def pointAddDoubleDenState7 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleDenState6 yst out left right) 1568 32

def pointAddDoubleDenArgsState (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleDenState7 yst out left right)
    (pointAddDoubleLeftPtr yst out left right + 64).toNat 32

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem pointAddDoubleDenState2_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddDoubleDenState2 yst out left right).memory =
      (pointAddDoubleXSqState yst out left right).memory := by
  simp [pointAddDoubleDenState2, pointAddDoubleDenState1]

@[simp] private theorem pointAddDoubleDenState4_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddDoubleDenState4 yst out left right).memory =
      (pointAddDoubleXSqState yst out left right).memory := by
  simp [pointAddDoubleDenState4, pointAddDoubleDenState3]

@[simp] private theorem pointAddDoubleDenState6_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddDoubleDenState6 yst out left right).memory =
      (pointAddDoubleXSqState yst out left right).memory := by
  simp [pointAddDoubleDenState6, pointAddDoubleDenState5]

private theorem step_pointAddDoubleDenLo2 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleXSqState yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])
      (.vals [pointAddDoubleLeftYLo yst out left right]
        (pointAddDoubleDenState2 yst out left right)) := by
  simpa [pointAddDoubleLeftYLo, pointAddDoubleLeftPtr,
    pointAddDoubleDenState1, pointAddDoubleDenState2] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddDoubleXSqState yst out left right) 1568 96)

private theorem step_pointAddDoubleDenHi2 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleDenState2 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])
      (.vals [pointAddDoubleLeftYHi yst out left right]
        (pointAddDoubleDenState4 yst out left right)) := by
  simpa [pointAddDoubleLeftYHi, pointAddDoubleLeftPtr,
    pointAddDoubleDenState3, pointAddDoubleDenState4] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddDoubleDenState2 yst out left right) 1568 64)

private theorem step_pointAddDoubleDenLo1 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleDenState4 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])
      (.vals [pointAddDoubleLeftYLo yst out left right]
        (pointAddDoubleDenState6 yst out left right)) := by
  simpa [pointAddDoubleLeftYLo, pointAddDoubleLeftPtr,
    pointAddDoubleDenState5, pointAddDoubleDenState6] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddDoubleDenState4 yst out left right) 1568 96)

private theorem step_pointAddDoubleDenHi1 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleDenState6 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])
      (.vals [pointAddDoubleLeftYHi yst out left right]
        (pointAddDoubleDenArgsState yst out left right)) := by
  simpa [pointAddDoubleLeftYHi, pointAddDoubleLeftPtr,
    pointAddDoubleDenState7, pointAddDoubleDenArgsState] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddDoubleDenState6 yst out left right) 1568 64)

theorem step_pointAddDoubleDenArgs {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleXSqState yst out left right) pointAddDoubleDenArgs
      (.vals [pointAddDoubleLeftYHi yst out left right,
        pointAddDoubleLeftYLo yst out left right,
        pointAddDoubleLeftYHi yst out left right,
        pointAddDoubleLeftYLo yst out left right]
        (pointAddDoubleDenArgsState yst out left right)) := by
  have hlo2 := step_pointAddDoubleDenLo2 (funs := funs) (V := V)
    yst out left right
  have hhi2 := step_pointAddDoubleDenHi2 (funs := funs) (V := V)
    yst out left right
  have hlo1 := step_pointAddDoubleDenLo1 (funs := funs) (V := V)
    yst out left right
  have hhi1 := step_pointAddDoubleDenHi1 (funs := funs) (V := V)
    yst out left right
  rw [pointAddDoubleDenArgs_eq]
  exact Step.argsCons
    (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hlo2) hhi2)
      hlo1) hhi1

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
