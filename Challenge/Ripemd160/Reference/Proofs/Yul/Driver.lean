import Challenge.Ripemd160.Reference.Proofs.Yul.Algorithm
import Challenge.Ripemd160.Reference.Proofs.Bytecode.HashSpecBridge
import YulEvmCompiler.Optimizer.Implementation.ReuseValuesSound

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Source-level RIPEMD-160 driver correctness

This layer connects the exact Yul procedure contracts to byte-oriented
padding and the mathematical RIPEMD-160 hash.  It contains no EVM execution
trace and no gas argument.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Yul.Driver

open YulSemantics
open YulSemantics.EVM
open EvmSemantics
open StateModel
open Challenge.YulProof.EvmState
open Algorithm
open Challenge.Ripemd160.Reference.Proofs.Bytecode
open YulEvmCompiler
open YulEvmCompiler.Optimizer.ReuseValues

/-- The sixteen-word schedule read directly from a byte array. -/
def blockWords (padded : ByteArray) (blockOff : Nat) (i : Nat) : UInt32 :=
  (CompressionCorrect.schedule padded blockOff)[i]!

theorem blockWords_eq_readLE32 (padded : ByteArray) (blockOff i : Nat)
    (hi : i < 16) :
    blockWords padded blockOff i =
      Crypto.Ripemd160.readLE32 padded (blockOff + i * 4) := by
  unfold blockWords
  interval_cases i <;>
    simp [CompressionCorrect.schedule, List.range']

private theorem byteOf_loadWord (memory : Nat → UInt8) (p i : Nat) (hi : i < 32) :
    ((loadWord memory p >>> (248 - 8 * i)) &&& 0xff) =
      BitVec.ofNat 256 (memory (p + i)).toNat := by
  have h := congrArg (fun bytes => bytes.getD i 0)
    (wordBytes_loadWord memory p)
  simp [wordBytes, readBytes, List.getD, hi] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (memory (p + i)).toNat_lt (by norm_num))]
  unfold byteAt at h
  have hshift : 248 - 8 * i = 8 * (31 - i) := by omega
  rw [hshift, Nat.shiftRight_eq_div_pow]
  change (loadWord memory p).toNat / 2 ^ (8 * (31 - i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have hn := congrArg UInt8.toNat h
  simpa [Nat.shiftRight_eq_div_pow] using hn

private theorem readLE32_eq_bytes (bs : ByteArray) (off : Nat) :
    Crypto.Ripemd160.readLE32 bs off =
      let b0 := (bs[off]?.getD 0).toUInt32
      let b1 := (bs[off + 1]?.getD 0).toUInt32
      let b2 := (bs[off + 2]?.getD 0).toUInt32
      let b3 := (bs[off + 3]?.getD 0).toUInt32
      (b0 ||| (b1 <<< UInt32.ofNat 8)) |||
        ((b2 <<< UInt32.ofNat 16) ||| (b3 <<< UInt32.ofNat 24)) := by
  unfold Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl_cons, List.foldl_nil]
  have hbyte (i : Nat) :
      (if h : off + i < bs.size then bs[off + i].toUInt32 else 0) =
        (bs[off + i]?.getD 0).toUInt32 := by
    by_cases h : off + i < bs.size <;> simp [h]
  rw [hbyte 0, hbyte 1, hbyte 2, hbyte 3]
  norm_num
  rw [UInt32.or_assoc]
  rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.shiftLeft_zero]

/-- The Yul four-byte reader agrees with the mathematical RIPEMD reader on
matching functional and finite byte memories. -/
theorem readLE32Value_eq_readLE32 {memory : Nat → UInt8} {bs : ByteArray}
    (hmem : MemMatch memory bs) (off : U256) :
    readLE32Value memory off =
      BitVec.ofNat 256 (Crypto.Ripemd160.readLE32 bs off.toNat).toNat := by
  rw [readLE32Value]
  rw [byteOf_loadWord memory off.toNat 0 (by omega),
    byteOf_loadWord memory off.toNat 1 (by omega),
    byteOf_loadWord memory off.toNat 2 (by omega),
    byteOf_loadWord memory off.toNat 3 (by omega),
    readLE32_eq_bytes]
  have hb0 := hmem off.toNat
  have hb1 := hmem (off.toNat + 1)
  have hb2 := hmem (off.toNat + 2)
  have hb3 := hmem (off.toNat + 3)
  rw [← getD_eq_dite] at hb0 hb1 hb2 hb3
  simp only [Nat.add_zero]
  rw [hb0, hb1, hb2, hb3]
  generalize bs[off.toNat]?.getD 0 = b0
  generalize bs[off.toNat + 1]?.getD 0 = b1
  generalize bs[off.toNat + 2]?.getD 0 = b2
  generalize bs[off.toNat + 3]?.getD 0 = b3
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat',
    UInt8.toNat_toUInt32]
  norm_num only [Nat.reducePow, Nat.reduceMod]
  have hs8 : b1.toNat <<< 8 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := b1.toNat_lt
    norm_num at ⊢
    omega
  have hs16 : b2.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := b2.toNat_lt
    norm_num at ⊢
    omega
  have hs24 : b3.toNat <<< 24 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := b3.toNat_lt
    norm_num at ⊢
    omega
  have hb0' : b0.toNat < 2 ^ 256 := Nat.lt_trans b0.toNat_lt (by norm_num)
  have hb1' : b1.toNat < 2 ^ 256 := Nat.lt_trans b1.toNat_lt (by norm_num)
  have hb2' : b2.toNat < 2 ^ 256 := Nat.lt_trans b2.toNat_lt (by norm_num)
  have hb3' : b3.toNat < 2 ^ 256 := Nat.lt_trans b3.toNat_lt (by norm_num)
  have hs8' : b1.toNat <<< 8 < 2 ^ 256 := Nat.lt_trans hs8 (by norm_num)
  have hs16' : b2.toNat <<< 16 < 2 ^ 256 := Nat.lt_trans hs16 (by norm_num)
  have hs24' : b3.toNat <<< 24 < 2 ^ 256 := Nat.lt_trans hs24 (by norm_num)
  norm_num at hb0' hb1' hb2' hb3' hs8 hs16 hs24 hs8' hs16' hs24'
  rw [Nat.mod_eq_of_lt hb0', Nat.mod_eq_of_lt hb1', Nat.mod_eq_of_lt hb2',
    Nat.mod_eq_of_lt hb3', Nat.mod_eq_of_lt hs8', Nat.mod_eq_of_lt hs16',
    Nat.mod_eq_of_lt hs24', Nat.mod_eq_of_lt hs8, Nat.mod_eq_of_lt hs16,
    Nat.mod_eq_of_lt hs24]
  have hall : b0.toNat ||| b1.toNat <<< 8 |||
      (b2.toNat <<< 16 ||| b3.toNat <<< 24) < 2 ^ 256 := Nat.lt_trans
    (Nat.or_lt_two_pow
      (Nat.or_lt_two_pow (Nat.lt_trans b0.toNat_lt (by norm_num)) hs8)
      (Nat.or_lt_two_pow hs16 hs24))
    (by norm_num : 2 ^ 32 < 2 ^ 256)
  norm_num at hall
  rw [Nat.mod_eq_of_lt hall]

/-- A four-byte local slice is enough to connect the source reader to the
mathematical byte-array reader. -/
theorem readLE32Value_eq_readLE32_of_bytes {memory : Nat → UInt8}
    {bs : ByteArray} (off : U256) (blockOff : Nat)
    (h0 : memory off.toNat = bs[blockOff]?.getD 0)
    (h1 : memory (off.toNat + 1) = bs[blockOff + 1]?.getD 0)
    (h2 : memory (off.toNat + 2) = bs[blockOff + 2]?.getD 0)
    (h3 : memory (off.toNat + 3) = bs[blockOff + 3]?.getD 0) :
    readLE32Value memory off =
      BitVec.ofNat 256 (Crypto.Ripemd160.readLE32 bs blockOff).toNat := by
  rw [readLE32Value]
  rw [byteOf_loadWord memory off.toNat 0 (by omega),
    byteOf_loadWord memory off.toNat 1 (by omega),
    byteOf_loadWord memory off.toNat 2 (by omega),
    byteOf_loadWord memory off.toNat 3 (by omega),
    readLE32_eq_bytes]
  simp only [Nat.add_zero]
  rw [h0, h1, h2, h3]
  generalize bs[blockOff]?.getD 0 = b0
  generalize bs[blockOff + 1]?.getD 0 = b1
  generalize bs[blockOff + 2]?.getD 0 = b2
  generalize bs[blockOff + 3]?.getD 0 = b3
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat',
    UInt8.toNat_toUInt32]
  norm_num only [Nat.reducePow, Nat.reduceMod]
  have hs8 : b1.toNat <<< 8 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := b1.toNat_lt
    norm_num at ⊢
    omega
  have hs16 : b2.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := b2.toNat_lt
    norm_num at ⊢
    omega
  have hs24 : b3.toNat <<< 24 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := b3.toNat_lt
    norm_num at ⊢
    omega
  have hb0' : b0.toNat < 2 ^ 256 := Nat.lt_trans b0.toNat_lt (by norm_num)
  have hb1' : b1.toNat < 2 ^ 256 := Nat.lt_trans b1.toNat_lt (by norm_num)
  have hb2' : b2.toNat < 2 ^ 256 := Nat.lt_trans b2.toNat_lt (by norm_num)
  have hb3' : b3.toNat < 2 ^ 256 := Nat.lt_trans b3.toNat_lt (by norm_num)
  have hs8' : b1.toNat <<< 8 < 2 ^ 256 := Nat.lt_trans hs8 (by norm_num)
  have hs16' : b2.toNat <<< 16 < 2 ^ 256 := Nat.lt_trans hs16 (by norm_num)
  have hs24' : b3.toNat <<< 24 < 2 ^ 256 := Nat.lt_trans hs24 (by norm_num)
  norm_num at hb0' hb1' hb2' hb3' hs8 hs16 hs24 hs8' hs16' hs24'
  rw [Nat.mod_eq_of_lt hb0', Nat.mod_eq_of_lt hb1', Nat.mod_eq_of_lt hb2',
    Nat.mod_eq_of_lt hb3', Nat.mod_eq_of_lt hs8', Nat.mod_eq_of_lt hs16',
    Nat.mod_eq_of_lt hs24', Nat.mod_eq_of_lt hs8, Nat.mod_eq_of_lt hs16,
    Nat.mod_eq_of_lt hs24]
  have hall : b0.toNat ||| b1.toNat <<< 8 |||
      (b2.toNat <<< 16 ||| b3.toNat <<< 24) < 2 ^ 256 := Nat.lt_trans
    (Nat.or_lt_two_pow
      (Nat.or_lt_two_pow (Nat.lt_trans b0.toNat_lt (by norm_num)) hs8)
      (Nat.or_lt_two_pow hs16 hs24))
    (by norm_num : 2 ^ 32 < 2 ^ 256)
  norm_num at hall
  rw [Nat.mod_eq_of_lt hall]

/-- Every word installed by `initTables` can be read independently of the
incoming memory. -/
theorem loadWord_initTables (st : EvmState) (p v : U256)
    (hmember : (p, v) ∈ tableStores)
    (hall : ∀ q w, (q, w) ∈ tableStores →
      (q = p ∧ w = v) ∨ WordDisjoint q p) :
    loadWord (initTablesState st).memory p.toNat = v := by
  exact loadWord_storeMany_member st tableStores p v hmember hall

private theorem tableStores_disjoint_slot (slot : Nat) (hslot : slot < 22) :
    ∀ q w, (q, w) ∈ tableStores →
      (q = BitVec.ofNat 256 (0x4a0 + slot * 32) ∧
        w = (tableStores[slot]!).2) ∨
      WordDisjoint q (BitVec.ofNat 256 (0x4a0 + slot * 32)) := by
  interval_cases slot <;> intro q w hm <;>
    simp only [tableStores, List.mem_cons, List.not_mem_nil, or_false] at hm <;>
    rcases hm with h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h <;>
    cases h <;> simp only [WordDisjoint] <;> decide

private theorem loadWord_initTableSlot (st : EvmState) (slot : Nat)
    (hslot : slot < 22) :
    loadWord (initTablesState st).memory (0x4a0 + slot * 32) =
      (tableStores[slot]!).2 := by
  have h := loadWord_initTables st
    (BitVec.ofNat 256 (0x4a0 + slot * 32)) (tableStores[slot]!).2
    (by interval_cases slot <;> decide)
    (tableStores_disjoint_slot slot hslot)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  exact h

/-- The fixed permutation, rotation, and constant regions installed by
`initTables`, separated from the per-block message schedule. -/
structure FixedLookupCorrect (memory : Nat → UInt8) : Prop where
  leftIndex : ∀ i, i < 80 →
    tableValue memory 0x4a0 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.r[i]!)
  rightIndex : ∀ i, i < 80 →
    tableValue memory 0x500 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.rP[i]!)
  leftRotation : ∀ i, i < 80 →
    tableValue memory 0x560 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.s[i]!)
  rightRotation : ∀ i, i < 80 →
    tableValue memory 0x5c0 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.sP[i]!)
  leftConstant : ∀ i, i < 80 →
    loadWord memory (0x620 + BitVec.ofNat 256 (i / 16) * 32).toNat =
      BitVec.ofNat 256 (Crypto.Ripemd160.K[i / 16]!).toNat
  rightConstant : ∀ i, i < 80 →
    loadWord memory (0x6c0 + BitVec.ofNat 256 (i / 16) * 32).toNat =
      BitVec.ofNat 256 (Crypto.Ripemd160.KP[i / 16]!).toNat

private theorem tableValue_nat (memory : Nat → UInt8) (base : U256)
    (baseNat i : Nat) (hi : i < 80) (hbase : base.toNat = baseNat)
    (hroom : baseNat + 96 < 2 ^ 256) :
    tableValue memory base (BitVec.ofNat 256 i) =
      (loadWord memory (baseNat + (i / 32) * 32) >>>
        (248 - 8 * (i % 32))) &&& 0xff := by
  unfold tableValue
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hi (by norm_num : 80 < 2 ^ 256))]
  have h32 : (32 : U256).toNat = 32 := by decide
  rw [hbase, h32]
  rw [Nat.mod_eq_of_lt (by omega : i / 32 * 32 < 2 ^ 256)]
  rw [Nat.mod_eq_of_lt (by omega : baseNat + i / 32 * 32 < 2 ^ 256)]
  rw [if_neg (by have := Nat.mod_lt i (by omega : 0 < 32); omega)]

private theorem tableValue_4a0_nat (memory : Nat → UInt8) (i : Nat)
    (hi : i < 80) :
    tableValue memory 0x4a0 (BitVec.ofNat 256 i) =
      (loadWord memory (0x4a0 + (i / 32) * 32) >>>
        (248 - 8 * (i % 32))) &&& 0xff := by
  exact tableValue_nat memory 0x4a0 0x4a0 i hi (by decide) (by norm_num)

private theorem initTables_leftIndex (st : EvmState) :
    ∀ i, i < 80 → tableValue (initTablesState st).memory 0x4a0
      (BitVec.ofNat 256 i) = BitVec.ofNat 256 (Crypto.Ripemd160.r[i]!) := by
  intro i hi
  rw [tableValue_4a0_nat _ i hi]
  interval_cases i <;> norm_num
  all_goals first
    | rw [loadWord_initTableSlot st 0 (by decide)]
    | rw [loadWord_initTableSlot st 1 (by decide)]
    | rw [loadWord_initTableSlot st 2 (by decide)]
  all_goals decide

private theorem initTables_rightIndex (st : EvmState) :
    ∀ i, i < 80 → tableValue (initTablesState st).memory 0x500
      (BitVec.ofNat 256 i) = BitVec.ofNat 256 (Crypto.Ripemd160.rP[i]!) := by
  intro i hi
  rw [tableValue_nat _ 0x500 0x500 i hi (by decide) (by norm_num)]
  interval_cases i <;> norm_num
  all_goals first
    | rw [loadWord_initTableSlot st 3 (by decide)]
    | rw [loadWord_initTableSlot st 4 (by decide)]
    | rw [loadWord_initTableSlot st 5 (by decide)]
  all_goals decide

private theorem initTables_leftRotation (st : EvmState) :
    ∀ i, i < 80 → tableValue (initTablesState st).memory 0x560
      (BitVec.ofNat 256 i) = BitVec.ofNat 256 (Crypto.Ripemd160.s[i]!) := by
  intro i hi
  rw [tableValue_nat _ 0x560 0x560 i hi (by decide) (by norm_num)]
  interval_cases i <;> norm_num
  all_goals first
    | rw [loadWord_initTableSlot st 6 (by decide)]
    | rw [loadWord_initTableSlot st 7 (by decide)]
    | rw [loadWord_initTableSlot st 8 (by decide)]
  all_goals decide

private theorem initTables_rightRotation (st : EvmState) :
    ∀ i, i < 80 → tableValue (initTablesState st).memory 0x5c0
      (BitVec.ofNat 256 i) = BitVec.ofNat 256 (Crypto.Ripemd160.sP[i]!) := by
  intro i hi
  rw [tableValue_nat _ 0x5c0 0x5c0 i hi (by decide) (by norm_num)]
  interval_cases i <;> norm_num
  all_goals first
    | rw [loadWord_initTableSlot st 9 (by decide)]
    | rw [loadWord_initTableSlot st 10 (by decide)]
    | rw [loadWord_initTableSlot st 11 (by decide)]
  all_goals decide

private theorem constantAddress_nat (memory : Nat → UInt8) (base : U256)
    (baseNat i : Nat) (hi : i < 80) (hbase : base.toNat = baseNat)
    (hroom : baseNat + 160 < 2 ^ 256) :
    loadWord memory (base + BitVec.ofNat 256 (i / 16) * 32).toNat =
      loadWord memory (baseNat + (i / 16) * 32) := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [hbase, Nat.mod_eq_of_lt (by omega : i / 16 < 2 ^ 256)]
  have h32 : (32 : U256).toNat = 32 := by decide
  rw [h32, Nat.mod_eq_of_lt (by omega : i / 16 * 32 < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : baseNat + i / 16 * 32 < 2 ^ 256)]

private theorem initTables_leftConstant (st : EvmState) :
    ∀ i, i < 80 →
      loadWord (initTablesState st).memory
          (0x620 + BitVec.ofNat 256 (i / 16) * 32).toNat =
        BitVec.ofNat 256 (Crypto.Ripemd160.K[i / 16]!).toNat := by
  intro i hi
  rw [constantAddress_nat _ 0x620 0x620 i hi (by decide) (by norm_num)]
  interval_cases i <;> norm_num
  all_goals first
    | rw [loadWord_initTableSlot st 12 (by decide)]
    | rw [loadWord_initTableSlot st 13 (by decide)]
    | rw [loadWord_initTableSlot st 14 (by decide)]
    | rw [loadWord_initTableSlot st 15 (by decide)]
    | rw [loadWord_initTableSlot st 16 (by decide)]
  all_goals decide

private theorem initTables_rightConstant (st : EvmState) :
    ∀ i, i < 80 →
      loadWord (initTablesState st).memory
          (0x6c0 + BitVec.ofNat 256 (i / 16) * 32).toNat =
        BitVec.ofNat 256 (Crypto.Ripemd160.KP[i / 16]!).toNat := by
  intro i hi
  rw [constantAddress_nat _ 0x6c0 0x6c0 i hi (by decide) (by norm_num)]
  interval_cases i <;> norm_num
  all_goals first
    | rw [loadWord_initTableSlot st 17 (by decide)]
    | rw [loadWord_initTableSlot st 18 (by decide)]
    | rw [loadWord_initTableSlot st 19 (by decide)]
    | rw [loadWord_initTableSlot st 20 (by decide)]
    | rw [loadWord_initTableSlot st 21 (by decide)]
  all_goals decide

/-- Exact fixed lookup data after the source initializer. -/
theorem fixedLookup_initTables (st : EvmState) :
    FixedLookupCorrect (initTablesState st).memory :=
  ⟨initTables_leftIndex st, initTables_rightIndex st,
    initTables_leftRotation st, initTables_rightRotation st,
    initTables_leftConstant st, initTables_rightConstant st⟩

/-- The generic upward frame relation, named for this driver's use. -/
abbrev MemoryEqAbove := MemoryEqFrom

private theorem scheduleStep_above (cutoff : Nat) (msgOff : U256)
    (st : EvmState) (i : Nat) (hi : i < 16) (hcutoff : 0x4a0 ≤ cutoff) :
    MemoryEqAbove cutoff st (scheduleStepState msgOff st i) := by
  unfold scheduleStepState xSetState
  apply MemoryEqFrom.storeWordAt
  · exact MemoryEqFrom.touch cutoff st _ _
  · simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have hbase : (0x2a0 : U256).toNat = 0x2a0 := by decide
    have h32 : (32 : U256).toNat = 32 := by decide
    rw [hbase, h32, Nat.mod_eq_of_lt (by omega : i < 2 ^ 256),
      Nat.mod_eq_of_lt (by omega : i * 32 < 2 ^ 256),
      Nat.mod_eq_of_lt (by omega : 0x2a0 + i * 32 < 2 ^ 256)]
    omega

theorem schedulePrefix_above (cutoff : Nat) (msgOff : U256)
    (st : EvmState) (n : Nat) (hn : n ≤ 16) (hcutoff : 0x4a0 ≤ cutoff) :
    MemoryEqAbove cutoff st (schedulePrefix msgOff st n) := by
  induction n with
  | zero => exact MemoryEqFrom.refl cutoff st
  | succ n ih =>
      exact MemoryEqFrom.trans (ih (by omega))
        (scheduleStep_above cutoff msgOff _ n (by omega) hcutoff)

theorem FixedLookupCorrect.transport {before after : EvmState}
    (fixed : FixedLookupCorrect before.memory)
    (h : MemoryEqAbove 0x4a0 before after) :
    FixedLookupCorrect after.memory where
  leftIndex i hi := by
    rw [tableValue_nat _ 0x4a0 0x4a0 i hi (by decide) (by norm_num),
      h.loadWord _ (by omega)]
    have hf := fixed.leftIndex i hi
    rw [tableValue_nat _ 0x4a0 0x4a0 i hi (by decide) (by norm_num)] at hf
    exact hf
  rightIndex i hi := by
    rw [tableValue_nat _ 0x500 0x500 i hi (by decide) (by norm_num),
      h.loadWord _ (by omega)]
    have hf := fixed.rightIndex i hi
    rw [tableValue_nat _ 0x500 0x500 i hi (by decide) (by norm_num)] at hf
    exact hf
  leftRotation i hi := by
    rw [tableValue_nat _ 0x560 0x560 i hi (by decide) (by norm_num),
      h.loadWord _ (by omega)]
    have hf := fixed.leftRotation i hi
    rw [tableValue_nat _ 0x560 0x560 i hi (by decide) (by norm_num)] at hf
    exact hf
  rightRotation i hi := by
    rw [tableValue_nat _ 0x5c0 0x5c0 i hi (by decide) (by norm_num),
      h.loadWord _ (by omega)]
    have hf := fixed.rightRotation i hi
    rw [tableValue_nat _ 0x5c0 0x5c0 i hi (by decide) (by norm_num)] at hf
    exact hf
  leftConstant i hi := by
    rw [constantAddress_nat _ 0x620 0x620 i hi (by decide) (by norm_num),
      h.loadWord _ (by omega)]
    have hf := fixed.leftConstant i hi
    rw [constantAddress_nat _ 0x620 0x620 i hi (by decide) (by norm_num)] at hf
    exact hf
  rightConstant i hi := by
    rw [constantAddress_nat _ 0x6c0 0x6c0 i hi (by decide) (by norm_num),
      h.loadWord _ (by omega)]
    have hf := fixed.rightConstant i hi
    rw [constantAddress_nat _ 0x6c0 0x6c0 i hi (by decide) (by norm_num)] at hf
    exact hf

def initialHash : Compression.HashState :=
  { h0 := 0x67452301, h1 := 0xefcdab89, h2 := 0x98badcfe,
    h3 := 0x10325476, h4 := 0xc3d2e1f0 }

@[simp] theorem hashArray_initialHash :
    CompressionCorrect.hashArray initialHash = Crypto.Ripemd160.H0 := by
  rfl

private theorem loadWord_hSetState_nat (st : EvmState) (i j : Nat) (v : U256)
    (hi : i < 5) (hj : j < 5) :
    loadWord (hSetState st (BitVec.ofNat 256 i) v).memory (0x20 + j * 32) =
      if j = i then v &&& 0xffffffff else
        loadWord st.memory (0x20 + j * 32) := by
  unfold hSetState Challenge.YulProof.EvmState.storeWordAt
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h32 : (32 : U256).toNat = 32 := by decide
  simp only [h32]
  have haddr := Nat.mod_eq_of_lt (show 32 + i * 32 < 2 ^ 256 by omega)
  norm_num only [Nat.reducePow] at haddr
  rw [haddr]
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl,
      YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord]
  · rw [if_neg hji,
      YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
    omega

private theorem workingAt_hSetState_nat (st : EvmState) (i : Nat) (v : U256)
    (hi : i < 5) :
    workingAt (hSetState st (BitVec.ofNat 256 i) v).memory 0x020 =
      setSourceWorking (workingAt st.memory 0x020) i v := by
  apply sourceWorking_ext
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 0 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 1 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 2 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 3 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 4 v hi (by omega))

/-- `initH` installs exactly the mathematical RIPEMD initial state. -/
theorem workingAt_initHState (st : EvmState) :
    workingAt (initHState st).memory 0x020 =
      sourceWorkingOf (CompressionCorrect.workingOfHash initialHash) := by
  unfold initHState
  change workingAt
    (hSetState
      (hSetState
        (hSetState
          (hSetState
            (hSetState st (BitVec.ofNat 256 0) 0x67452301)
            (BitVec.ofNat 256 1) 0xefcdab89)
          (BitVec.ofNat 256 2) 0x98badcfe)
        (BitVec.ofNat 256 3) 0x10325476)
      (BitVec.ofNat 256 4) 0xc3d2e1f0).memory 0x020 = _
  rw [workingAt_hSetState_nat _ 4 _ (by omega),
    workingAt_hSetState_nat _ 3 _ (by omega),
    workingAt_hSetState_nat _ 2 _ (by omega),
    workingAt_hSetState_nat _ 1 _ (by omega),
    workingAt_hSetState_nat _ 0 _ (by omega)]
  simp [setSourceWorking, sourceWorkingOf, CompressionCorrect.workingOfHash,
    initialHash]

private theorem hSetState_above (cutoff : Nat) (st : EvmState) (i v : U256)
    (hi : i.toNat < 5) (hcutoff : 0xc0 ≤ cutoff) :
    MemoryEqAbove cutoff st (hSetState st i v) := by
  unfold hSetState
  apply MemoryEqFrom.storeWordAt (MemoryEqFrom.refl cutoff st)
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  have h20 : (0x20 : U256).toNat = 0x20 := by decide
  rw [h20, Nat.mod_eq_of_lt (by omega : i.toNat * 32 < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : 0x20 + i.toNat * 32 < 2 ^ 256)]
  omega

theorem initHState_above (cutoff : Nat) (st : EvmState) (hcutoff : 0xc0 ≤ cutoff) :
    MemoryEqAbove cutoff st (initHState st) := by
  unfold initHState
  apply MemoryEqFrom.trans
    (hSetState_above cutoff st 0 0x67452301 (by decide) hcutoff)
  apply MemoryEqFrom.trans
    (hSetState_above cutoff _ 1 0xefcdab89 (by decide) hcutoff)
  apply MemoryEqFrom.trans
    (hSetState_above cutoff _ 2 0x98badcfe (by decide) hcutoff)
  apply MemoryEqFrom.trans
    (hSetState_above cutoff _ 3 0x10325476 (by decide) hcutoff)
  exact hSetState_above cutoff _ 4 0xc3d2e1f0 (by decide) hcutoff

private theorem xAddress_eq (i : Nat) (hi : i < 16) :
    (0x2a0 + BitVec.ofNat 256 i * 32 : U256).toNat = 0x2a0 + i * 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hbase : (0x2a0 : U256).toNat = 0x2a0 := by decide
  have h32 : (32 : U256).toNat = 32 := by decide
  rw [hbase, h32, Nat.mod_eq_of_lt (by omega : i < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : i * 32 < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : 0x2a0 + i * 32 < 2 ^ 256)]

private theorem messageAddress_eq (msgBase i : Nat) (hi : i < 16)
    (hroom : msgBase + 64 < 2 ^ 256) :
    (BitVec.ofNat 256 msgBase + BitVec.ofNat 256 i * 4 : U256).toNat =
      msgBase + i * 4 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h4 : (4 : U256).toNat = 4 := by decide
  rw [h4, Nat.mod_eq_of_lt (by omega : msgBase < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : i * 4 < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : msgBase + i * 4 < 2 ^ 256)]

private theorem loadWord_scheduleStep_slot (st : EvmState) (msgOff : U256)
    (step i : Nat) (hstep : step < 16) (hi : i < 16) :
    loadWord (scheduleStepState msgOff st step).memory (0x2a0 + i * 32) =
      if i = step then readLE32Value st.memory
          (msgOff + BitVec.ofNat 256 step * 4) &&& 0xffffffff
      else loadWord st.memory (0x2a0 + i * 32) := by
  unfold scheduleStepState xSetState Challenge.YulProof.EvmState.storeWordAt
  rw [xAddress_eq step hstep]
  by_cases his : i = step
  · subst i
    rw [if_pos rfl,
      YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord]
  · rw [if_neg his,
      YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
    · rfl
    · omega

/-- Exact source schedule slots, retaining the message bytes from the state
before the loop. -/
theorem schedulePrefix_slots (st : EvmState) (msgBase n : Nat)
    (hn : n ≤ 16) (hbase : 0x800 ≤ msgBase)
    (hroom : msgBase + 64 < 2 ^ 256) :
    ∀ i, i < n →
      loadWord (schedulePrefix (BitVec.ofNat 256 msgBase) st n).memory
          (0x2a0 + i * 32) =
        readLE32Value st.memory
            (BitVec.ofNat 256 msgBase + BitVec.ofNat 256 i * 4) &&& 0xffffffff := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      rw [schedulePrefix, loadWord_scheduleStep_slot _ _ n i (by omega) (by omega)]
      by_cases hin : i = n
      · subst i
        rw [if_pos rfl]
        unfold readLE32Value
        rw [(schedulePrefix_above 0x800 (BitVec.ofNat 256 msgBase) st n
          (by omega) (by omega)).loadWord]
        rw [messageAddress_eq msgBase n (by omega) hroom]
        omega
      · rw [if_neg hin]
        exact ih (by omega) i (by omega)

def BlockBytesAt (memory : Nat → UInt8) (msgBase : Nat)
    (padded : ByteArray) (blockOff : Nat) : Prop :=
  ∀ k, k < 64 → memory (msgBase + k) = padded[blockOff + k]?.getD 0

/-- The source schedule together with the initialized fixed data supplies the
complete lookup contract consumed by one compression proof. -/
theorem lookupCorrect_afterSchedule (st : EvmState) (msgBase blockOff : Nat)
    (padded : ByteArray) (hbase : 0x800 ≤ msgBase)
    (hroom : msgBase + 64 < 2 ^ 256)
    (hbytes : BlockBytesAt st.memory msgBase padded blockOff)
    (fixed : FixedLookupCorrect st.memory) :
    LookupCorrect (scheduleState (BitVec.ofNat 256 msgBase) st).memory
      (blockWords padded blockOff) where
  schedule i hi := by
    rw [xAddress_eq i hi, scheduleState,
      schedulePrefix_slots st msgBase 16 (by omega) hbase hroom i hi]
    rw [blockWords_eq_readLE32 padded blockOff i hi]
    rw [readLE32Value_eq_readLE32_of_bytes
      (BitVec.ofNat 256 msgBase + BitVec.ofNat 256 i * 4)
      (blockOff + i * 4)]
    · exact embedded_mask _
    · rw [messageAddress_eq msgBase i hi hroom]
      exact hbytes (i * 4) (by omega)
    · rw [messageAddress_eq msgBase i hi hroom]
      simpa [Nat.add_assoc] using hbytes (i * 4 + 1) (by omega)
    · rw [messageAddress_eq msgBase i hi hroom]
      simpa [Nat.add_assoc] using hbytes (i * 4 + 2) (by omega)
    · rw [messageAddress_eq msgBase i hi hroom]
      simpa [Nat.add_assoc] using hbytes (i * 4 + 3) (by omega)
  leftIndex := (fixed.transport
    (schedulePrefix_above 0x4a0 (BitVec.ofNat 256 msgBase) st 16
      (by omega) (by omega))).leftIndex
  rightIndex := (fixed.transport
    (schedulePrefix_above 0x4a0 (BitVec.ofNat 256 msgBase) st 16
      (by omega) (by omega))).rightIndex
  leftRotation := (fixed.transport
    (schedulePrefix_above 0x4a0 (BitVec.ofNat 256 msgBase) st 16
      (by omega) (by omega))).leftRotation
  rightRotation := (fixed.transport
    (schedulePrefix_above 0x4a0 (BitVec.ofNat 256 msgBase) st 16
      (by omega) (by omega))).rightRotation
  leftConstant := (fixed.transport
    (schedulePrefix_above 0x4a0 (BitVec.ofNat 256 msgBase) st 16
      (by omega) (by omega))).leftConstant
  rightConstant := (fixed.transport
    (schedulePrefix_above 0x4a0 (BitVec.ofNat 256 msgBase) st 16
      (by omega) (by omega))).rightConstant

/-- The generic downward frame relation, named for this driver's use. -/
abbrev MemoryEqBelow := MemoryEqBefore

private theorem scheduleStep_below (cutoff : Nat) (msgOff : U256)
    (st : EvmState) (i : Nat) (hi : i < 16) (hcutoff : cutoff ≤ 0x2a0) :
    MemoryEqBelow cutoff st (scheduleStepState msgOff st i) := by
  unfold scheduleStepState xSetState
  apply MemoryEqBefore.storeWordAt
  · intro p hp
    rfl
  · rw [xAddress_eq i hi]
    omega

theorem schedulePrefix_below (cutoff : Nat) (msgOff : U256)
    (st : EvmState) (n : Nat) (hn : n ≤ 16) (hcutoff : cutoff ≤ 0x2a0) :
    MemoryEqBelow cutoff st (schedulePrefix msgOff st n) := by
  induction n with
  | zero => exact MemoryEqBefore.refl cutoff st
  | succ n ih =>
      exact MemoryEqBefore.trans (ih (by omega))
        (scheduleStep_below cutoff msgOff _ n (by omega) hcutoff)

theorem workingAt_scheduleState (st : EvmState) (msgOff : U256) :
    workingAt (scheduleState msgOff st).memory 0x020 =
      workingAt st.memory 0x020 := by
  have h := schedulePrefix_below 0x200 msgOff st 16 (by omega) (by omega)
  apply sourceWorking_ext
  · exact h.loadWord 32 (by omega)
  · exact h.loadWord 64 (by omega)
  · exact h.loadWord 96 (by omega)
  · exact h.loadWord 128 (by omega)
  · exact h.loadWord 160 (by omega)

/-- One complete source `compress` transition refines the pure RIPEMD model. -/
theorem compressionState_refines (st : EvmState) (msgBase blockOff : Nat)
    (padded : ByteArray) (h : Compression.HashState)
    (hbase : 0x800 ≤ msgBase) (hroom : msgBase + 64 < 2 ^ 256)
    (hbytes : BlockBytesAt st.memory msgBase padded blockOff)
    (fixed : FixedLookupCorrect st.memory)
    (hhash : workingAt st.memory 0x020 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h)) :
    workingAt
        (compressionState st (BitVec.ofNat 256 msgBase)).memory 0x020 =
      sourceHashOf (CompressionCorrect.compressModel
        (blockWords padded blockOff) h) := by
  apply compressionState_correct
  · exact lookupCorrect_afterSchedule st msgBase blockOff padded
      hbase hroom hbytes fixed
  · rw [workingAt_scheduleState]
    exact hhash

private theorem highMemoryEq_to_above {before after : EvmState}
    (h : HighMemoryEq before after) (cutoff : Nat) (hcutoff : 0x200 ≤ cutoff) :
    MemoryEqAbove cutoff before after := by
  intro p hp
  exact h p (by omega)

private theorem addThreeMasked_above (cutoff : Nat) (st : EvmState)
    (p q r : U256) : MemoryEqAbove cutoff st (addThreeMasked st p q r).2 := by
  intro _ _
  rfl

private theorem compressionTailState_above (cutoff : Nat) (st : EvmState)
    (hcutoff : 0xc0 ≤ cutoff) :
    MemoryEqAbove cutoff st (compressionTailState st) := by
  let t := addThreeMasked st 0x220 0x100 0x1c0
  let p1 := addThreeMasked t.2 0x240 0x120 0x1e0
  let s1 := hSetState p1.2 1 p1.1
  let p2 := addThreeMasked s1 0x260 0x140 0x160
  let s2 := hSetState p2.2 2 p2.1
  let p3 := addThreeMasked s2 0x280 0x0c0 0x180
  let s3 := hSetState p3.2 3 p3.1
  let p4 := addThreeMasked s3 0x200 0x0e0 0x1a0
  let s4 := hSetState p4.2 4 p4.1
  change MemoryEqAbove cutoff st (hSetState s4 0 t.1)
  apply MemoryEqFrom.trans (addThreeMasked_above cutoff st _ _ _)
  apply MemoryEqFrom.trans (addThreeMasked_above cutoff t.2 _ _ _)
  apply MemoryEqFrom.trans (hSetState_above cutoff p1.2 1 p1.1 (by decide) hcutoff)
  apply MemoryEqFrom.trans (addThreeMasked_above cutoff s1 _ _ _)
  apply MemoryEqFrom.trans (hSetState_above cutoff p2.2 2 p2.1 (by decide) hcutoff)
  apply MemoryEqFrom.trans (addThreeMasked_above cutoff s2 _ _ _)
  apply MemoryEqFrom.trans (hSetState_above cutoff p3.2 3 p3.1 (by decide) hcutoff)
  apply MemoryEqFrom.trans (addThreeMasked_above cutoff s3 _ _ _)
  apply MemoryEqFrom.trans (hSetState_above cutoff p4.2 4 p4.1 (by decide) hcutoff)
  exact hSetState_above cutoff s4 0 t.1 (by decide) hcutoff

private theorem compressionWorkState_above (cutoff : Nat) (st : EvmState)
    (msgOff : U256) (hcutoff : 0x4a0 ≤ cutoff) :
    MemoryEqAbove cutoff st (compressionWorkState st msgOff) := by
  let s0 := scheduleState msgOff st
  let s1 := mcopyState s0 0x0c0 0x020 0x0a0
  let s2 := mcopyState s1 0x160 0x020 0x0a0
  let s3 := mcopyState s2 0x200 0x020 0x0a0
  let s4 := leftRoundPrefix 80 s3
  let s5 := rightRoundPrefix 80 s4
  have h0c0 : (0x0c0 : U256).toNat = 0x0c0 := by decide
  have h160 : (0x160 : U256).toNat = 0x160 := by decide
  have h200 : (0x200 : U256).toNat = 0x200 := by decide
  have h0a0 : (0x0a0 : U256).toNat = 0x0a0 := by decide
  change MemoryEqAbove cutoff st s5
  apply MemoryEqFrom.trans
    (schedulePrefix_above cutoff msgOff st 16 (by omega) hcutoff)
  apply MemoryEqFrom.trans (MemoryEqFrom.mcopyState cutoff s0 0x0c0 0x020 0x0a0 (by
    rw [h0c0, h0a0]; omega))
  apply MemoryEqFrom.trans (MemoryEqFrom.mcopyState cutoff s1 0x160 0x020 0x0a0 (by
    rw [h160, h0a0]; omega))
  apply MemoryEqFrom.trans (MemoryEqFrom.mcopyState cutoff s2 0x200 0x020 0x0a0 (by
    rw [h200, h0a0]; omega))
  apply MemoryEqFrom.trans
    (highMemoryEq_to_above (highMemoryEq_leftRoundPrefix s3 80) cutoff (by omega))
  exact highMemoryEq_to_above (highMemoryEq_rightRoundPrefix s4 80) cutoff (by omega)

/-- A full source compression call changes no byte in the padded-message
region (nor in any higher address). -/
theorem compressionState_above (cutoff : Nat) (st : EvmState) (msgOff : U256)
    (hcutoff : 0x4a0 ≤ cutoff) :
    MemoryEqAbove cutoff st (compressionState st msgOff) := by
  unfold compressionState
  exact MemoryEqFrom.trans (compressionWorkState_above cutoff st msgOff hcutoff)
    (compressionTailState_above cutoff _ (by omega))

def PaddedBytesAt (memory : Nat → UInt8) (padded : ByteArray) : Prop :=
  ∀ k, k < padded.size → memory (0x800 + k) = padded[k]?.getD 0

def compressPrefix (st : EvmState) : Nat → EvmState
  | 0 => st
  | n + 1 => compressionState (compressPrefix st n)
      (BitVec.ofNat 256 (0x800 + n * 64))

def hashPrefix (padded : ByteArray) : Nat → Compression.HashState
  | 0 => initialHash
  | n + 1 => CompressionCorrect.compressModel
      (blockWords padded (n * 64)) (hashPrefix padded n)

structure PrefixCorrect (initial : EvmState) (padded : ByteArray) (n : Nat) : Prop where
  hash : workingAt (compressPrefix initial n).memory 0x020 =
    sourceWorkingOf (CompressionCorrect.workingOfHash (hashPrefix padded n))
  fixed : FixedLookupCorrect (compressPrefix initial n).memory
  padded : PaddedBytesAt (compressPrefix initial n).memory padded

/-- The source block loop carries only three compact invariants: five hash
words, immutable fixed lookup data, and the padded byte image. -/
theorem compressPrefix_correct (initial : EvmState) (padded : ByteArray)
    (n : Nat) (hblocks : n * 64 ≤ padded.size)
    (hroom : 0x800 + padded.size < 2 ^ 256)
    (hhash : workingAt initial.memory 0x020 =
      sourceWorkingOf (CompressionCorrect.workingOfHash initialHash))
    (hfixed : FixedLookupCorrect initial.memory)
    (hpadded : PaddedBytesAt initial.memory padded) :
    PrefixCorrect initial padded n := by
  induction n with
  | zero => exact ⟨hhash, hfixed, hpadded⟩
  | succ n ih =>
      have prev := ih (by omega)
      let current := compressPrefix initial n
      have hblock : BlockBytesAt current.memory (0x800 + n * 64)
          padded (n * 64) := by
        intro k hk
        simpa [current, Nat.add_assoc] using prev.padded (n * 64 + k) (by omega)
      have hmsgroom : 0x800 + n * 64 + 64 < 2 ^ 256 := by omega
      have hstep := compressionState_refines current (0x800 + n * 64)
        (n * 64) padded (hashPrefix padded n) (by omega) hmsgroom
        hblock prev.fixed prev.hash
      have hframe4a0 := compressionState_above 0x4a0 current
        (BitVec.ofNat 256 (0x800 + n * 64)) (by omega)
      have hframe800 := compressionState_above 0x800 current
        (BitVec.ofNat 256 (0x800 + n * 64)) (by omega)
      constructor
      · simpa [compressPrefix, hashPrefix, current, sourceHashOf, sourceWorkingOf,
          CompressionCorrect.workingOfHash] using hstep
      · simpa [compressPrefix, current] using prev.fixed.transport hframe4a0
      · intro k hk
        rw [show (compressPrefix initial (n + 1)) =
          compressionState current (BitVec.ofNat 256 (0x800 + n * 64)) by rfl]
        rw [hframe800 (0x800 + k) (by omega)]
        exact prev.padded k hk

theorem hashArray_hashPrefix (padded : ByteArray) (n : Nat) :
    CompressionCorrect.hashArray (hashPrefix padded n) =
      SpecBridge.absorbBlocks Crypto.Ripemd160.H0 padded 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [hashPrefix, SpecBridge.absorbBlocks_succ]
      rw [show CompressionCorrect.hashArray
          (CompressionCorrect.compressModel (blockWords padded (n * 64))
            (hashPrefix padded n)) =
        Crypto.Ripemd160.compressBlock
          (CompressionCorrect.hashArray (hashPrefix padded n)) padded (n * 64) by
        change CompressionCorrect.hashArray
            (CompressionCorrect.compressModel
              (fun i => (CompressionCorrect.schedule padded (n * 64))[i]!)
              (hashPrefix padded n)) = _
        exact CompressionCorrect.compressModel_eq_compressBlock padded (n * 64)
          (hashPrefix padded n)]
      rw [ih]
      congr 2
      omega

end Challenge.Ripemd160.Reference.Proofs.Yul.Driver
