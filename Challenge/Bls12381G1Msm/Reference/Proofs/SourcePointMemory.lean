import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddTotal

set_option warningAsError true

/-!
Fixed memory-region facts for the G1MSM point helper.

The concrete program keeps every point in one of the four disjoint 128-byte
regions `[0x800,0x880)`, `[0x880,0x900)`, `[0x900,0x980)`, and
`[0x980,0xa00)`.  Its field scratch and pointer slots end below `0x800`.
This module turns that high-water separation into small opaque facts; later
proofs need not normalize the pointer-dependent `touchMemory` DAG.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- Touching a range already below the active-memory high-water mark is a
state no-op. -/
theorem touchMemory_eq_of_range_end_le (yst : EvmState) (offset size : Nat)
    (hend : offset + size ≤ 32 * yst.activeWords.toNat) :
    touchMemory yst offset size = yst := by
  unfold touchMemory activeWordsAfter
  by_cases hsize : size = 0
  · simp [hsize]
  · rw [if_neg hsize]
    have hpositive : 0 < yst.activeWords.toNat := by omega
    have hlast : offset + size - 1 < 32 * yst.activeWords.toNat := by omega
    have hquot : (offset + size - 1) / 32 < yst.activeWords.toNat := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 32)).2
      simpa [Nat.mul_comm] using hlast
    have hmax : yst.activeWords.toNat.max
        ((offset + size - 1) / 32 + 1) = yst.activeWords.toNat :=
      Nat.max_eq_left (by omega)
    rw [hmax, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The exact point regions used by the concrete G1MSM runtime have already
been activated.  Address bounds are kept on the evaluated word addresses so
the theorem also records that no 256-bit pointer addition wrapped. -/
structure PointAddFixedLayout (yst : EvmState) (out left right : U256) : Prop where
  active : 80 ≤ (pointAddXEqState yst out left right).activeWords.toNat
  leftXHi : (pointAddUnequalLeftPtr yst out left right).toNat + 32 ≤ 2560
  leftXLo : (pointAddUnequalLeftPtr yst out left right + 32).toNat + 32 ≤ 2560
  leftYHi : (pointAddUnequalLeftPtr yst out left right + 64).toNat + 32 ≤ 2560
  leftYLo : (pointAddUnequalLeftPtr yst out left right + 96).toNat + 32 ≤ 2560
  rightXHi : (pointAddUnequalRightPtr yst out left right).toNat + 32 ≤ 2560
  rightXLo : (pointAddUnequalRightPtr yst out left right + 32).toNat + 32 ≤ 2560
  rightYHi : (pointAddUnequalRightPtr yst out left right + 64).toNat + 32 ≤ 2560
  rightYLo : (pointAddUnequalRightPtr yst out left right + 96).toNat + 32 ≤ 2560

private theorem touchMemory_eq_of_fixed_active (yst : EvmState)
    (offset : Nat) (hactive : 80 ≤ yst.activeWords.toNat)
    (hend : offset + 32 ≤ 2560) : touchMemory yst offset 32 = yst := by
  apply touchMemory_eq_of_range_end_le
  omega

/-- Once the 128-byte point regions are active, the denominator's x-coordinate
loads cannot change the state left by the numerator's y-coordinate loads. -/
theorem pointAddUnequalInputsState_eq_of_fixed_layout (yst : EvmState)
    (out left right : U256) (hlayout : PointAddFixedLayout yst out left right) :
    pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right := by
  have hslot1568 : 1568 + 32 ≤ 2560 := by norm_num
  have hslot1600 : 1600 + 32 ≤ 2560 := by norm_num
  have hnumerator : pointAddUnequalNumeratorInputsState yst out left right =
      pointAddXEqState yst out left right := by
    unfold pointAddUnequalNumeratorInputsState pointAddUnequalNumeratorState7
      pointAddUnequalNumeratorState6 pointAddUnequalNumeratorState5
      pointAddUnequalNumeratorState4 pointAddUnequalNumeratorState3
      pointAddUnequalNumeratorState2 pointAddUnequalNumeratorState1
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1568]
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.leftYLo]
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1568]
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.leftYHi]
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1600]
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.rightYLo]
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1600]
    rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.rightYHi]
  unfold pointAddUnequalDenominatorInputsState
    pointAddUnequalDenominatorState7 pointAddUnequalDenominatorState6
    pointAddUnequalDenominatorState5 pointAddUnequalDenominatorState4
    pointAddUnequalDenominatorState3 pointAddUnequalDenominatorState2
    pointAddUnequalDenominatorState1
  rw [hnumerator]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1568]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.leftXLo]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1568]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.leftXHi]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1600]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.rightXLo]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hslot1600]
  rw [touchMemory_eq_of_fixed_active _ _ hlayout.active hlayout.rightXHi]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
