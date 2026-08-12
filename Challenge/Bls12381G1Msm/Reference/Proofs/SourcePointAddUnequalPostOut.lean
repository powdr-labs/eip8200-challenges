import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostludeBridge
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointMemoryPointers
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpInvMemory
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option warningAsError true

/-! Cached output-pointer preservation through unequal affine addition. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem loadWord_storeWord_same (memory : Nat → UInt8) (slot : Nat)
    (value : U256) : loadWord (storeWord memory slot value) slot = value :=
  YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord
    memory slot value

private theorem loadWord_storeWord_disjoint (memory : Nat → UInt8)
    (writtenSlot untouchedSlot : Nat) (value : U256)
    (hdisjoint : writtenSlot + 32 ≤ untouchedSlot ∨
      untouchedSlot + 32 ≤ writtenSlot) :
    loadWord (storeWord memory writtenSlot value) untouchedSlot =
      loadWord memory untouchedSlot :=
  YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other
    memory writtenSlot untouchedSlot value hdisjoint

theorem pointAddPrefixState_out (yst : EvmState) (out left right : U256) :
    loadWord (pointAddPrefixState yst out left right).memory 1536 = out := by
  simp only [pointAddPrefixState, pointAddStore]
  rw [loadWord_storeWord_disjoint _ 1600 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1568 1536 _ (by omega),
    loadWord_storeWord_same]

theorem pointAddUnequalNumeratorInputsState_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalNumeratorInputsState yst out left right).memory
      1536 = out := by
  rw [pointAddUnequalNumeratorInputsState_memory_eq_prefix,
    pointAddPrefixState_out]

theorem pointAddUnequalInvFinalState_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalInvFinalState yst out left right).memory 1536 =
      out := by
  rw [pointAddUnequalInvFinalState,
    fpInvFinalState_loadWord_after_scratch _ _ _ 1536 (by omega),
    pointAddUnequalNumeratorInputsState_out]

theorem pointAddUnequalLambdaState_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalLambdaState yst out left right).memory 1536 =
      out := by
  rw [pointAddUnequalLambdaState,
    fpMulFinalState_loadWord_after_scratch _ _ _ _ _ 1536 (by omega),
    pointAddUnequalInvFinalState_out]

theorem pointAddUnequalX3State_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalX3State yst out left right).memory 1536 = out := by
  rw [pointAddUnequalX3State,
    fpMulFinalState_loadWord_after_scratch _ _ _ _ _ 1536 (by omega),
    pointAddUnequalLambdaState_out]

private theorem pointAddUnequalXSubLeftState1_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalXSubLeftState1 yst out left right).memory =
      (pointAddUnequalX3State yst out left right).memory := by
  rw [pointAddUnequalXSubLeftState1,
    pointAddUnequal_touchMemory_memory]

private theorem pointAddUnequalXSubLeftState2_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalXSubLeftState2 yst out left right).memory =
      (pointAddUnequalXSubLeftState1 yst out left right).memory := by
  rw [pointAddUnequalXSubLeftState2,
    pointAddUnequal_touchMemory_memory]

private theorem pointAddUnequalXSubLeftState3_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalXSubLeftState3 yst out left right).memory =
      (pointAddUnequalXSubLeftState2 yst out left right).memory := by
  rw [pointAddUnequalXSubLeftState3,
    pointAddUnequal_touchMemory_memory]

theorem pointAddUnequalXSubLeftRawState_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalXSubLeftRawState yst out left right).memory =
      (pointAddUnequalX3State yst out left right).memory := by
  rw [show (pointAddUnequalXSubLeftRawState yst out left right).memory =
      (pointAddUnequalXSubLeftState3 yst out left right).memory by
        rw [pointAddUnequalXSubLeftRawState,
          pointAddUnequal_touchMemory_memory],
    pointAddUnequalXSubLeftState3_memory,
    pointAddUnequalXSubLeftState2_memory,
    pointAddUnequalXSubLeftState1_memory]

private theorem pointAddUnequalXSubRightState1_memory
    (ctx : PointAddUnequalXSubRightContext) :
    (pointAddUnequalXSubRightState1 ctx).memory = ctx.state.memory := by
  rw [pointAddUnequalXSubRightState1,
    pointAddUnequal_touchMemory_memory]

private theorem pointAddUnequalXSubRightState2_memory
    (ctx : PointAddUnequalXSubRightContext) :
    (pointAddUnequalXSubRightState2 ctx).memory =
      (pointAddUnequalXSubRightState1 ctx).memory := by
  rw [pointAddUnequalXSubRightState2,
    pointAddUnequal_touchMemory_memory]

private theorem pointAddUnequalXSubRightState3_memory
    (ctx : PointAddUnequalXSubRightContext) :
    (pointAddUnequalXSubRightState3 ctx).memory =
      (pointAddUnequalXSubRightState2 ctx).memory := by
  rw [pointAddUnequalXSubRightState3,
    pointAddUnequal_touchMemory_memory]

theorem pointAddUnequalXSubRightRawState_memory
    (ctx : PointAddUnequalXSubRightContext) :
    (pointAddUnequalXSubRightRawState ctx).memory = ctx.state.memory := by
  rw [show (pointAddUnequalXSubRightRawState ctx).memory =
      (pointAddUnequalXSubRightState3 ctx).memory by
        rw [pointAddUnequalXSubRightRawState,
          pointAddUnequal_touchMemory_memory],
    pointAddUnequalXSubRightState3_memory,
    pointAddUnequalXSubRightState2_memory,
    pointAddUnequalXSubRightState1_memory]

theorem pointAddUnequalXSubState_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalXSubState yst out left right).memory 1536 = out := by
  rw [pointAddUnequalXSubState,
    pointAddUnequalXSubRightRawState_memory,
    show (pointAddUnequalXSubRightContext yst out left right).state =
      pointAddUnequalXSubLeftRawState yst out left right by rfl,
    pointAddUnequalXSubLeftRawState_memory,
    pointAddUnequalX3State_out]

theorem pointAddUnequalDeltaRawState_memory
    (ctx : PointAddUnequalDeltaContext) :
    (pointAddUnequalDeltaRawState ctx).memory = ctx.state.memory := by
  rfl

theorem pointAddUnequalDeltaConcreteState_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalDeltaConcreteState yst out left right).memory
      1536 = out := by
  rw [pointAddUnequalDeltaConcreteState,
    pointAddUnequalDeltaRawState_memory,
    show (pointAddUnequalDeltaContext yst out left right).state =
      pointAddUnequalXSubState yst out left right by rfl,
    pointAddUnequalXSubState_out]

theorem pointAddUnequalYMulState_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalYMulState yst out left right).memory 1536 = out := by
  rw [pointAddUnequalYMulState,
    fpMulFinalState_loadWord_after_scratch _ _ _ _ _ 1536 (by omega),
    pointAddUnequalDeltaConcreteState_out]

theorem pointAddUnequalYSubRawState_memory (ctx : PointAddUnequalYSubContext) :
    (pointAddUnequalYSubRawState ctx).memory = ctx.state.memory := by
  rfl

theorem pointAddUnequalYSubConcreteState_out (yst : EvmState)
    (out left right : U256) :
    loadWord (pointAddUnequalYSubConcreteState yst out left right).memory
      1536 = out := by
  rw [pointAddUnequalYSubConcreteState,
    pointAddUnequalYSubRawState_memory,
    show (pointAddUnequalYSubContext yst out left right).state =
      pointAddUnequalYMulState yst out left right by rfl,
    pointAddUnequalYMulState_out]

theorem pointAddUnequalPostOut_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalPostOut (pointAddUnequalPostContext yst out left right) =
      out := by
  rw [pointAddUnequalPostOut]
  exact pointAddUnequalYSubConcreteState_out yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
