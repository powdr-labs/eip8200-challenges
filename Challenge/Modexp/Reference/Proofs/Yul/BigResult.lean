import Challenge.Modexp.Reference.Proofs.Yul.BigMath
import Challenge.Modexp.Reference.Proofs.Yul.BigPath
import Challenge.YulProof.NatDigits

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Mathematical result bridge for the direct MODEXP big path

The relational execution proof ends in the exact state transformers from
`BigPath`.  This file interprets those transformers as integers and bytes.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigResult

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open BigMath

theorem limbCount_toNat (m : Nat) (hm : m ≤ 1024) :
    (BigPath.limbCount (BitVec.ofNat 256 m)).toNat = Limbs.limbCount m := by
  unfold BigPath.limbCount Limbs.limbCount
  rw [BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 256)]
  change ((m + 31) % 2 ^ 256) / 32 = (m + 31) / 32
  rw [Nat.mod_eq_of_lt (by omega : m + 31 < 2 ^ 256)]

theorem readLimb_of_represents {memory : Nat → UInt8} {ptr count value index : Nat}
    (hrep : Represents memory ptr count value) (hindex : index < count) :
    (loadWord memory (ptr + 32 * index)).toNat =
      value / Limbs.radix ^ index % Limbs.radix := by
  have hget := Challenge.YulProof.NatDigits.getElem_eq_div_mod_ofDigits Limbs.radix
      (memoryLimbs memory ptr count) index Limbs.radix_pos
      (by simpa using hindex)
      (fun digit hdigit => memoryLimb_lt memory ptr count hdigit)
  rw [value_of_represents hrep] at hget
  simpa [memoryLimbs] using hget

theorem serializeLimbAddress_toNat (m k : Nat) (hm : m ≤ 1024) (hk : k < m) :
    (serializeLimbAddress (BitVec.ofNat 256 m) k).toNat =
      0x0800 + 32 * ((m - 1 - k) / 32) := by
  have hm256 : m < 2 ^ 256 := by omega
  have hk256 : k < 2 ^ 256 := by omega
  have hrev :
      (BitVec.ofNat 256 m - 1 - BitVec.ofNat 256 k).toNat = m - 1 - k := by
    rw [BitVec.toNat_sub_of_le, BitVec.toNat_sub_of_le]
    · change m % 2 ^ 256 - 1 - k % 2 ^ 256 = m - 1 - k
      rw [Nat.mod_eq_of_lt hm256, Nat.mod_eq_of_lt hk256]
    · simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm256]
      omega
    · simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm256,
        Nat.mod_eq_of_lt hk256]
      omega
  simp only [serializeLimbAddress]
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, hrev]
  have h2048 : (2048 : U256).toNat = 2048 := rfl
  have h32 : (32 : U256).toNat = 32 := rfl
  rw [h2048, h32,
    Nat.mod_eq_of_lt (by omega : (m - 1 - k) / 32 * 32 < 2 ^ 256)]
  rw [Nat.mod_eq_of_lt (by omega :
    0x0800 + (m - 1 - k) / 32 * 32 < 2 ^ 256)]
  omega

theorem serializeByteShift_eq (m k : Nat) (hm : m ≤ 1024) (hk : k < m) :
    serializeByteShift (BitVec.ofNat 256 m) k =
      ((m - 1 - k) % 32) * 8 := by
  have hm256 : m < 2 ^ 256 := by omega
  have hk256 : k < 2 ^ 256 := by omega
  have hrev :
      (BitVec.ofNat 256 m - 1 - BitVec.ofNat 256 k).toNat = m - 1 - k := by
    rw [BitVec.toNat_sub_of_le, BitVec.toNat_sub_of_le]
    · change m % 2 ^ 256 - 1 - k % 2 ^ 256 = m - 1 - k
      rw [Nat.mod_eq_of_lt hm256, Nat.mod_eq_of_lt hk256]
    · simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm256]
      omega
    · simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm256,
        Nat.mod_eq_of_lt hk256]
      omega
  simp only [serializeByteShift]
  rw [BitVec.toNat_mul, BitVec.toNat_umod, hrev]
  change ((m - 1 - k) % 32 * 8) % 2 ^ 256 = (m - 1 - k) % 32 * 8
  rw [Nat.mod_eq_of_lt (by omega : (m - 1 - k) % 32 * 8 < 2 ^ 256)]

theorem serializedByte_correct (memory : Nat → UInt8) (m k value : Nat)
    (hm : m ≤ 1024) (hk : k < m)
    (hrep : Represents memory 0x0800 (Limbs.limbCount m) value) :
    ((loadWord memory
        (serializeLimbAddress (BitVec.ofNat 256 m) k).toNat >>>
          serializeByteShift (BitVec.ofNat 256 m) k) &&& 0xff).toNat =
      value / 256 ^ (m - 1 - k) % 256 := by
  let reverse := m - 1 - k
  let limb := reverse / 32
  let rem := reverse % 32
  have hlimb : limb < Limbs.limbCount m := by
    simp [limb, reverse, Limbs.limbCount]
    omega
  have hrem : rem < 32 := Nat.mod_lt _ (by omega)
  have hword := readLimb_of_represents hrep hlimb
  rw [serializeLimbAddress_toNat m k hm hk,
    serializeByteShift_eq m k hm hk, BitVec.toNat_and,
    BitVec.toNat_ushiftRight]
  change
    ((loadWord memory (2048 + 32 * ((m - 1 - k) / 32))).toNat >>>
      ((m - 1 - k) % 32 * 8)) &&& 255 = _
  rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (rem * 8) = 256 ^ rem by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
    congr 1
    omega]
  rw [hword]
  have hrecompose : 32 * limb + rem = reverse := by
    have h := Nat.mod_add_div reverse 32
    omega
  simpa [limb, rem, reverse, Limbs.radix_eq, hrecompose] using
    Challenge.YulProof.NatDigits.extractedWordByte value limb rem hrem

end Challenge.Modexp.Reference.Proofs.Yul.BigResult
