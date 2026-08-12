import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostOut
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option warningAsError true

/-! Exact four-word readback from the unequal affine-addition postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

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

private theorem pointAddUnequalPostStoreState_load_same
    (yst : EvmState) (offset value : U256) :
    loadWord (pointAddUnequalPostStoreState yst offset value).memory
      offset.toNat = value := by
  unfold pointAddUnequalPostStoreState
  exact loadWord_storeWord_same yst.memory offset.toNat value

private theorem pointAddUnequalPostStoreState_load_disjoint
    (yst : EvmState) (offset value : U256) (untouched : Nat)
    (hdisjoint : offset.toNat + 32 ≤ untouched ∨
      untouched + 32 ≤ offset.toNat) :
    loadWord (pointAddUnequalPostStoreState yst offset value).memory
      untouched = loadWord yst.memory untouched := by
  unfold pointAddUnequalPostStoreState
  exact loadWord_storeWord_disjoint yst.memory offset.toNat untouched value
    hdisjoint

private theorem pointAddUnequalPostState_loadXHi
    (ctx : PointAddUnequalPostContext)
    (hout : (pointAddUnequalPostOut ctx).toNat + 96 < 2 ^ 256) :
    loadWord (pointAddUnequalPostState ctx).memory
      (pointAddUnequalPostOut ctx).toNat = ctx.xHi := by
  have h32 : (pointAddUnequalPostOut ctx + 32).toNat =
      (pointAddUnequalPostOut ctx).toNat + 32 := by
    bv_omega
  have h64 : (pointAddUnequalPostOut ctx + 64).toNat =
      (pointAddUnequalPostOut ctx).toNat + 64 := by
    bv_omega
  have h96 : (pointAddUnequalPostOut ctx + 96).toNat =
      (pointAddUnequalPostOut ctx).toNat + 96 := by
    bv_omega
  rw [pointAddUnequalPostState,
    pointAddUnequalPostStoreState_load_disjoint _ _ _ _ (by
      right
      rw [h96]
      omega),
    pointAddUnequalPostState3,
    pointAddUnequalPostStoreState_load_disjoint _ _ _ _ (by
      right
      rw [h64]
      omega),
    pointAddUnequalPostState2,
    pointAddUnequalPostStoreState_load_disjoint _ _ _ _ (by
      right
      rw [h32]),
    pointAddUnequalPostState1,
    pointAddUnequalPostStoreState_load_same]

private theorem pointAddUnequalPostState_loadXLo
    (ctx : PointAddUnequalPostContext)
    (hout : (pointAddUnequalPostOut ctx).toNat + 96 < 2 ^ 256) :
    loadWord (pointAddUnequalPostState ctx).memory
      (pointAddUnequalPostOut ctx + 32).toNat = ctx.xLo := by
  have h32 : (pointAddUnequalPostOut ctx + 32).toNat =
      (pointAddUnequalPostOut ctx).toNat + 32 := by
    bv_omega
  have h64 : (pointAddUnequalPostOut ctx + 64).toNat =
      (pointAddUnequalPostOut ctx).toNat + 64 := by
    bv_omega
  have h96 : (pointAddUnequalPostOut ctx + 96).toNat =
      (pointAddUnequalPostOut ctx).toNat + 96 := by
    bv_omega
  rw [pointAddUnequalPostState,
    pointAddUnequalPostStoreState_load_disjoint _ _ _ _ (by
      right
      rw [h32, h96]
      omega),
    pointAddUnequalPostState3,
    pointAddUnequalPostStoreState_load_disjoint _ _ _ _ (by
      right
      rw [h32, h64]),
    pointAddUnequalPostState2,
    pointAddUnequalPostStoreState_load_same]

private theorem pointAddUnequalPostState_loadYHi
    (ctx : PointAddUnequalPostContext)
    (hout : (pointAddUnequalPostOut ctx).toNat + 96 < 2 ^ 256) :
    loadWord (pointAddUnequalPostState ctx).memory
      (pointAddUnequalPostOut ctx + 64).toNat = ctx.yHi := by
  have h64 : (pointAddUnequalPostOut ctx + 64).toNat =
      (pointAddUnequalPostOut ctx).toNat + 64 := by
    bv_omega
  have h96 : (pointAddUnequalPostOut ctx + 96).toNat =
      (pointAddUnequalPostOut ctx).toNat + 96 := by
    bv_omega
  rw [pointAddUnequalPostState,
    pointAddUnequalPostStoreState_load_disjoint _ _ _ _ (by
      right
      rw [h64, h96]),
    pointAddUnequalPostState3,
    pointAddUnequalPostStoreState_load_same]

private theorem pointAddUnequalPostState_loadYLo
    (ctx : PointAddUnequalPostContext) :
    loadWord (pointAddUnequalPostState ctx).memory
      (pointAddUnequalPostOut ctx + 96).toNat = ctx.yLo := by
  rw [pointAddUnequalPostState,
    pointAddUnequalPostStoreState_load_same]

theorem pointAddUnequalPostState_readback
    (ctx : PointAddUnequalPostContext)
    (hout : (pointAddUnequalPostOut ctx).toNat + 96 < 2 ^ 256) :
    pointMemoryX (pointAddUnequalPostState ctx)
        (pointAddUnequalPostOut ctx) =
      ({ hi := YulEvmCompiler.conv ctx.xHi
         lo := YulEvmCompiler.conv ctx.xLo } : Fp.Limbs) ∧
    pointMemoryY (pointAddUnequalPostState ctx)
        (pointAddUnequalPostOut ctx) =
      ({ hi := YulEvmCompiler.conv ctx.yHi
         lo := YulEvmCompiler.conv ctx.yLo } : Fp.Limbs) := by
  constructor
  · unfold pointMemoryX
    rw [pointAddUnequalPostState_loadXHi ctx hout,
      pointAddUnequalPostState_loadXLo ctx hout]
  · unfold pointMemoryY
    rw [pointAddUnequalPostState_loadYHi ctx hout,
      pointAddUnequalPostState_loadYLo ctx]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
