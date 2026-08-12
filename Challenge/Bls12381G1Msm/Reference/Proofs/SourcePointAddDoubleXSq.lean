import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYNonzero

set_option warningAsError true

/-! Staged loads for the first field multiplication in point doubling. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSqState1 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState yst out left right) 1568 32

def pointAddDoubleXSqState2 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState1 yst out left right)
    (pointAddFiniteLeftPtr yst out left right + 32).toNat 32

def pointAddDoubleXSqState3 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState2 yst out left right) 1568 32

def pointAddDoubleXSqState4 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState3 yst out left right)
    (pointAddFiniteLeftPtr yst out left right).toNat 32

def pointAddDoubleXSqState5 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState4 yst out left right) 1568 32

def pointAddDoubleXSqState6 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState5 yst out left right)
    (pointAddFiniteLeftPtr yst out left right + 32).toNat 32

def pointAddDoubleXSqState7 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState6 yst out left right) 1568 32

def pointAddDoubleXSqArgsState (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddDoubleXSqState7 yst out left right)
    (pointAddFiniteLeftPtr yst out left right).toNat 32

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem pointAddYSumState_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddYSumState yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddYSumState, pointAddYSumState7]

@[simp] private theorem pointAddDoubleXSqState2_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddDoubleXSqState2 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddDoubleXSqState2, pointAddDoubleXSqState1]

@[simp] private theorem pointAddDoubleXSqState4_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddDoubleXSqState4 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddDoubleXSqState4, pointAddDoubleXSqState3]

@[simp] private theorem pointAddDoubleXSqState6_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddDoubleXSqState6 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddDoubleXSqState6, pointAddDoubleXSqState5]

private theorem step_pointAddDoubleXSqLo2 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddYSumState yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])
      (.vals [pointAddFiniteLeftXLo yst out left right]
        (pointAddDoubleXSqState2 yst out left right)) := by
  simpa [pointAddFiniteLeftXLo, pointAddFiniteLeftPtr,
    pointAddDoubleXSqState1, pointAddDoubleXSqState2] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddYSumState yst out left right) 1568 32)

private theorem step_pointAddDoubleXSqHi2 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleXSqState2 yst out left right)
      (.builtin .mload [.builtin .mload [.lit (.number 1568)]])
      (.vals [pointAddFiniteLeftXHi yst out left right]
        (pointAddDoubleXSqState4 yst out left right)) := by
  simpa [pointAddFiniteLeftXHi, pointAddFiniteLeftPtr,
    pointAddDoubleXSqState3, pointAddDoubleXSqState4] using
    (step_nestedLoad (funs := funs) (V := V)
      (pointAddDoubleXSqState2 yst out left right) 1568)

private theorem step_pointAddDoubleXSqLo1 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleXSqState4 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])
      (.vals [pointAddFiniteLeftXLo yst out left right]
        (pointAddDoubleXSqState6 yst out left right)) := by
  simpa [pointAddFiniteLeftXLo, pointAddFiniteLeftPtr,
    pointAddDoubleXSqState5, pointAddDoubleXSqState6] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddDoubleXSqState4 yst out left right) 1568 32)

private theorem step_pointAddDoubleXSqHi1 {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddDoubleXSqState6 yst out left right)
      (.builtin .mload [.builtin .mload [.lit (.number 1568)]])
      (.vals [pointAddFiniteLeftXHi yst out left right]
        (pointAddDoubleXSqArgsState yst out left right)) := by
  simpa [pointAddFiniteLeftXHi, pointAddFiniteLeftPtr,
    pointAddDoubleXSqState7, pointAddDoubleXSqArgsState] using
    (step_nestedLoad (funs := funs) (V := V)
      (pointAddDoubleXSqState6 yst out left right) 1568)

theorem step_pointAddDoubleXSqArgs {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddYSumState yst out left right) pointAddDoubleXSqArgs
      (.vals [pointAddFiniteLeftXHi yst out left right,
        pointAddFiniteLeftXLo yst out left right,
        pointAddFiniteLeftXHi yst out left right,
        pointAddFiniteLeftXLo yst out left right]
        (pointAddDoubleXSqArgsState yst out left right)) := by
  have hlo2 := step_pointAddDoubleXSqLo2 (funs := funs) (V := V)
    yst out left right
  have hhi2 := step_pointAddDoubleXSqHi2 (funs := funs) (V := V)
    yst out left right
  have hlo1 := step_pointAddDoubleXSqLo1 (funs := funs) (V := V)
    yst out left right
  have hhi1 := step_pointAddDoubleXSqHi1 (funs := funs) (V := V)
    yst out left right
  rw [pointAddDoubleXSqArgs_eq]
  exact Step.argsCons
    (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hlo2) hhi2)
      hlo1) hhi1

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
