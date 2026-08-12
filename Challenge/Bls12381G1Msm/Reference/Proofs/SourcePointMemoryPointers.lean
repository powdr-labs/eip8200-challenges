import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointMemory
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulMemory
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option warningAsError true

/-! Stable read-only views of the fixed G1 point regions. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointMemoryX (yst : EvmState) (ptr : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (loadWord yst.memory ptr.toNat)
    lo := YulEvmCompiler.conv (loadWord yst.memory (ptr + 32).toNat) }

def pointMemoryY (yst : EvmState) (ptr : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (loadWord yst.memory (ptr + 64).toNat)
    lo := YulEvmCompiler.conv (loadWord yst.memory (ptr + 96).toNat) }

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

@[simp] theorem pointAddFiniteState_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddFiniteState yst out left right).memory =
      (pointAddPrefixState yst out left right).memory := by
  rfl

@[simp] theorem pointAddXEqState_memory_eq_prefix (yst : EvmState)
    (out left right : U256) :
    (pointAddXEqState yst out left right).memory =
      (pointAddPrefixState yst out left right).memory := by
  rfl

@[simp] theorem pointAddUnequalNumeratorInputsState_memory_eq_prefix
    (yst : EvmState) (out left right : U256) :
    (pointAddUnequalNumeratorInputsState yst out left right).memory =
      (pointAddPrefixState yst out left right).memory := by
  rw [pointAddUnequalNumeratorInputsState_memory,
    pointAddXEqState_memory_eq_prefix]

@[simp] theorem pointAddFiniteLeftPtr_eq (yst : EvmState)
    (out left right : U256) :
    pointAddFiniteLeftPtr yst out left right = left := by
  rw [pointAddFiniteLeftPtr, pointAddFiniteState_memory]
  simp only [pointAddPrefixState, pointAddStore]
  rw [loadWord_storeWord_disjoint _ 1600 1568 _ (by omega),
    loadWord_storeWord_same]

@[simp] theorem pointAddFiniteRightPtr_eq (yst : EvmState)
    (out left right : U256) :
    pointAddFiniteRightPtr yst out left right = right := by
  rw [pointAddFiniteRightPtr, pointAddFiniteState_memory]
  simp only [pointAddPrefixState, pointAddStore]
  rw [loadWord_storeWord_same]

@[simp] theorem pointAddUnequalLeftPtr_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalLeftPtr yst out left right = left := by
  rw [pointAddUnequalLeftPtr, pointAddXEqState_memory_eq_prefix]
  simp only [pointAddPrefixState, pointAddStore]
  rw [loadWord_storeWord_disjoint _ 1600 1568 _ (by omega),
    loadWord_storeWord_same]

@[simp] theorem pointAddUnequalRightPtr_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalRightPtr yst out left right = right := by
  rw [pointAddUnequalRightPtr, pointAddXEqState_memory_eq_prefix]
  simp only [pointAddPrefixState, pointAddStore]
  rw [loadWord_storeWord_same]

theorem pointAddPrefix_loadPoint (yst : EvmState)
    (out left right : U256) (address : Nat)
    (hregion : 1632 ≤ address) :
    loadWord (pointAddPrefixState yst out left right).memory
        address = loadWord yst.memory address := by
  simp only [pointAddPrefixState, pointAddStore]
  rw [loadWord_storeWord_disjoint _ 1600 _ _ (by left; omega),
    loadWord_storeWord_disjoint _ 1568 _ _ (by left; omega),
    loadWord_storeWord_disjoint _ 1536 _ _ (by left; omega)]

theorem pointAddUnequalLeftXLimbs_eq (yst : EvmState)
    (out left right : U256)
    (hhi : 1632 ≤ left.toNat) (hlo : 1632 ≤ (left + 32).toNat) :
    pointAddUnequalLeftXLimbs yst out left right = pointMemoryX yst left := by
  rw [pointAddUnequalLeftXLimbs, pointMemoryX]
  simp only [pointAddUnequalLeftXHi, pointAddUnequalLeftXLo,
    pointAddUnequalLeftPtr_eq,
    pointAddUnequalNumeratorInputsState_memory_eq_prefix]
  rw [pointAddPrefix_loadPoint yst out left right left.toNat hhi,
    pointAddPrefix_loadPoint yst out left right (left + 32).toNat hlo]

theorem pointAddUnequalRightXLimbs_eq (yst : EvmState)
    (out left right : U256)
    (hhi : 1632 ≤ right.toNat) (hlo : 1632 ≤ (right + 32).toNat) :
    pointAddUnequalRightXLimbs yst out left right = pointMemoryX yst right := by
  rw [pointAddUnequalRightXLimbs, pointMemoryX]
  simp only [pointAddUnequalRightXHi, pointAddUnequalRightXLo,
    pointAddUnequalRightPtr_eq,
    pointAddUnequalNumeratorInputsState_memory_eq_prefix]
  rw [pointAddPrefix_loadPoint yst out left right right.toNat hhi,
    pointAddPrefix_loadPoint yst out left right (right + 32).toNat hlo]

theorem pointAddFiniteLeftYLimbs_eq (yst : EvmState)
    (out left right : U256)
    (hhi : 1632 ≤ (left + 64).toNat)
    (hlo : 1632 ≤ (left + 96).toNat) :
    pointAddFiniteLeftYLimbs yst out left right = pointMemoryY yst left := by
  rw [pointAddFiniteLeftYLimbs, pointMemoryY]
  simp only [pointAddFiniteLeftYHi, pointAddFiniteLeftYLo,
    pointAddFiniteLeftPtr_eq, pointAddFiniteState_memory]
  rw [pointAddPrefix_loadPoint yst out left right (left + 64).toNat hhi,
    pointAddPrefix_loadPoint yst out left right (left + 96).toNat hlo]

theorem pointAddFiniteRightYLimbs_eq (yst : EvmState)
    (out left right : U256)
    (hhi : 1632 ≤ (right + 64).toNat)
    (hlo : 1632 ≤ (right + 96).toNat) :
    pointAddFiniteRightYLimbs yst out left right = pointMemoryY yst right := by
  rw [pointAddFiniteRightYLimbs, pointMemoryY]
  simp only [pointAddFiniteRightYHi, pointAddFiniteRightYLo,
    pointAddFiniteRightPtr_eq, pointAddFiniteState_memory]
  rw [pointAddPrefix_loadPoint yst out left right (right + 64).toNat hhi,
    pointAddPrefix_loadPoint yst out left right (right + 96).toNat hlo]

theorem pointAddDoubleXSqState_loadWord_after_scratch (yst : EvmState)
    (out left right : U256) (offset : Nat) (hstart : 1328 ≤ offset) :
    loadWord (pointAddDoubleXSqState yst out left right).memory offset =
      loadWord (pointAddPrefixState yst out left right).memory offset := by
  rw [pointAddDoubleXSqState,
    fpMulFinalState_loadWord_after_scratch _ _ _ _ _ offset hstart]
  rfl

@[simp] theorem pointAddDoubleLeftPtr_eq (yst : EvmState)
    (out left right : U256) :
    pointAddDoubleLeftPtr yst out left right = left := by
  rw [pointAddDoubleLeftPtr,
    pointAddDoubleXSqState_loadWord_after_scratch _ _ _ _ 1568 (by omega)]
  simp only [pointAddPrefixState, pointAddStore]
  rw [loadWord_storeWord_disjoint _ 1600 1568 _ (by omega),
    loadWord_storeWord_same]

theorem pointAddDoubleLeftYLimbs_eq (yst : EvmState)
    (out left right : U256)
    (hhi : 1632 ≤ (left + 64).toNat)
    (hlo : 1632 ≤ (left + 96).toNat) :
    pointAddDoubleLeftYLimbs yst out left right = pointMemoryY yst left := by
  rw [pointAddDoubleLeftYLimbs, pointMemoryY]
  simp only [pointAddDoubleLeftYHi, pointAddDoubleLeftYLo,
    pointAddDoubleLeftPtr_eq]
  rw [pointAddDoubleXSqState_loadWord_after_scratch _ _ _ _
      (left + 64).toNat (by omega),
    pointAddDoubleXSqState_loadWord_after_scratch _ _ _ _
      (left + 96).toNat (by omega),
    pointAddPrefix_loadPoint yst out left right (left + 64).toNat hhi,
    pointAddPrefix_loadPoint yst out left right (left + 96).toNat hlo]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
