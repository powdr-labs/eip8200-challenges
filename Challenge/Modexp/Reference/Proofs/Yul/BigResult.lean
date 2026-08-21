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

theorem outputAddress_toNat (i : Nat) (hi : i ≤ 1024) :
    ((0x1800 : U256) + BitVec.ofNat 256 i).toNat = 0x1800 + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
  change (6144 + i) % 2 ^ 256 = 6144 + i
  rw [Nat.mod_eq_of_lt (by omega)]

theorem serializeStep_preserves_represents (st : EvmState)
    (m i count value : Nat) (hm : m ≤ 1024) (hi : i < m)
    (hcount : count ≤ 32) (hrep : Represents st.memory 0x0800 count value) :
    Represents (serializeStep st (BitVec.ofNat 256 m) i).memory
      0x0800 count value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hj' : j < count := by simpa using hj
  let src := serializeLimbAddress (BitVec.ofNat 256 m) i
  let loaded := touchMemory st src.toNat 32
  let v := (loadWord st.memory src.toNat >>>
    serializeByteShift (BitVec.ofNat 256 m) i) &&& 0xff
  let dst : U256 := 0x1800 + BitVec.ofNat 256 i
  have hdst : dst.toNat = 0x1800 + i := outputAddress_toNat i (by omega)
  have hread : (BitVec.ofNat 256 (0x0800 + 32 * j)).toNat =
      0x0800 + 32 * j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpreserve := Challenge.YulProof.EvmState.loadWord_storeByteAt_other
    loaded dst (BitVec.ofNat 256 (0x0800 + 32 * j)) v (by
      right
      rw [hdst, hread]
      omega)
  have hpreserve' : loadWord (Challenge.YulProof.EvmState.storeByteAt loaded dst v).memory
      (BitVec.ofNat 256 (0x0800 + 32 * j)).toNat =
      loadWord st.memory (BitVec.ofNat 256 (0x0800 + 32 * j)).toNat := by
    simpa only [show loaded.memory = st.memory by rfl] using hpreserve
  change (loadWord (serializeStep st (BitVec.ofNat 256 m) i).memory
    (0x0800 + 32 * j)).toNat = _
  simpa [serializeStep, src, loaded, v, dst,
    Challenge.YulProof.EvmState.storeByteAt, hread] using congrArg BitVec.toNat hpreserve'

theorem serializePrefix_preserves_represents (st : EvmState)
    (m steps count value : Nat) (hm : m ≤ 1024) (hsteps : steps ≤ m)
    (hcount : count ≤ 32) (hrep : Represents st.memory 0x0800 count value) :
    Represents (serializePrefix (BitVec.ofNat 256 m) steps st).memory
      0x0800 count value := by
  induction steps with
  | zero => simpa [serializePrefix] using hrep
  | succ steps ih =>
      rw [serializePrefix]
      exact serializeStep_preserves_represents _ m steps count value hm (by omega)
        hcount (ih (by omega))

theorem serializePrefix_outputByte (st : EvmState) (m steps k value : Nat)
    (hm : m ≤ 1024) (hsteps : steps ≤ m) (hk : k < steps)
    (hrep : Represents st.memory 0x0800 (Limbs.limbCount m) value) :
    (serializePrefix (BitVec.ofNat 256 m) steps st).memory (0x1800 + k) =
      UInt8.ofNat (value / 256 ^ (m - 1 - k) % 256) := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      let before := serializePrefix (BitVec.ofNat 256 m) steps st
      let src := serializeLimbAddress (BitVec.ofNat 256 m) steps
      let v := (loadWord before.memory src.toNat >>>
        serializeByteShift (BitVec.ofNat 256 m) steps) &&& 0xff
      let dst : U256 := 0x1800 + BitVec.ofNat 256 steps
      have hsteps' : steps ≤ m := by omega
      have hdst : dst.toNat = 0x1800 + steps := outputAddress_toNat steps (by omega)
      rw [serializePrefix]
      change (storeByte before.memory dst.toNat v) (0x1800 + k) = _
      unfold storeByte
      by_cases hlast : k = steps
      · subst k
        rw [if_pos (by omega)]
        unfold byteAt
        congr 1
        have hbefore := serializePrefix_preserves_represents st m steps
          (Limbs.limbCount m) value hm hsteps'
          (Limbs.limbCount_le_32 m hm) hrep
        simpa [before, src, v] using
          serializedByte_correct before.memory m steps value hm (by omega) hbefore
      · rw [if_neg (by omega)]
        exact ih hsteps' (by omega)

theorem readBytes_serializedResultState (st : EvmState) (m value : Nat)
    (hm : m ≤ 1024)
    (hrep : Represents st.memory 0x0800 (Limbs.limbCount m) value) :
    readBytes (BigPath.serializedResultState st (BitVec.ofNat 256 m)).memory
      0x1800 m = (Precompile.natToBytes value m).toList := by
  unfold readBytes
  apply List.ext_get
  · rw [YulEvmCompiler.ByteArray.toList_eq_data]
    simp [Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < m := by simpa using hleft
    have hkbytes : k < (Precompile.natToBytes value m).size := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hk
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    have hrhs : (Precompile.natToBytes value m).toList[k] =
        (Precompile.natToBytes value m)[k]'hkbytes := by
      simpa only [YulEvmCompiler.ByteArray.toList_eq_data] using
        (show (Precompile.natToBytes value m).data.toList[k] =
            (Precompile.natToBytes value m).data[k] from Array.getElem_toList _).trans
          (ByteArray.getElem_eq_data_getElem _ hkbytes).symm
    rw [hrhs]
    change (BigPath.serializedResultState st (BitVec.ofNat 256 m)).memory
      (6144 + k) = (Precompile.natToBytes value m)[k]'hkbytes
    rw [show BigPath.serializedResultState st (BitVec.ofNat 256 m) =
      serializePrefix (BitVec.ofNat 256 m) m st by
        unfold BigPath.serializedResultState
        rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : m < 2 ^ 256)]]
    rw [serializePrefix_outputByte st m m k value hm (by rfl) hk hrep]
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hk),
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD value m k hk]

theorem returnedResultState_result (st : EvmState) (m value : Nat)
    (hm : m ≤ 1024)
    (hrep : Represents st.memory 0x0800 (Limbs.limbCount m) value) :
    (BigPath.returnedResultState st (BitVec.ofNat 256 m)).halted =
      some (HaltKind.ret, (Precompile.natToBytes value m).toList) := by
  change some (HaltKind.ret,
    readBytes (BigPath.serializedResultState st (BitVec.ofNat 256 m)).memory
      0x1800 (BitVec.ofNat 256 m).toNat) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 2 ^ 256),
    readBytes_serializedResultState st m value hm hrep]

end Challenge.Modexp.Reference.Proofs.Yul.BigResult
