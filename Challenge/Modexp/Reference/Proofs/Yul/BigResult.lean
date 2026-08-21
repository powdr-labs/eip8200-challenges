import Challenge.Modexp.Reference.Proofs.Yul.BigMath
import Challenge.Modexp.Reference.Proofs.Yul.BigFold
import Challenge.Modexp.Reference.Proofs.Yul.BigPath
import Challenge.Modexp.Reference.Proofs.Yul.WordMath
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

/-! ## Setup and modulus scan -/

@[simp] theorem modulusScanPrefix_memory (steps : Nat) (st : EvmState) :
    (modulusScanPrefix steps st).memory = st.memory := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [modulusScanPrefix, ih, YulSemantics.EVM.touchMemory]

theorem scannedModulusState_represents (st : EvmState)
    (modulusSize modOff : U256) (value : Nat)
    (hrep : Represents (BigPath.loadedModulusState st modulusSize modOff).memory
      (0x0000 : Nat) (BigPath.limbCount modulusSize).toNat value) :
    Represents (BigPath.scannedModulusState st modulusSize modOff).memory
      (0x0000 : Nat) (BigPath.limbCount modulusSize).toNat value := by
  simpa [BigPath.scannedModulusState] using hrep

theorem modulusOrPrefix_eq_zero_iff (count : Nat) (st : EvmState)
    (hcount : count ≤ 32) :
    modulusOrPrefix count st = 0 ↔
      memoryLimbs st.memory 0 count = List.replicate count 0 := by
  induction count with
  | zero => simp [modulusOrPrefix, memoryLimbs]
  | succ count ih =>
      rw [modulusOrPrefix, memoryLimbs_succ, List.replicate_succ']
      have haddr : (BitVec.ofNat 256 count * (32 : U256)).toNat =
          count * 32 := by
        rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
        change (count % 2 ^ 256 * 32) % 2 ^ 256 = count * 32
        rw [Nat.mod_eq_of_lt (show count < 2 ^ 256 by
          exact (by omega : count < 32).trans (by norm_num)),
          Nat.mod_eq_of_lt (show count * 32 < 2 ^ 256 by
            calc
              count * 32 < 32 * 32 := Nat.mul_lt_mul_of_pos_right
                (by omega) (by omega)
              _ < 2 ^ 256 := by norm_num)]
      constructor
      · intro hor
        have hparts : modulusOrPrefix count st = (0 : U256) ∧
            loadWord (modulusScanPrefix count st).memory
              (BitVec.ofNat 256 count * 32).toNat = 0 :=
          BitVec.or_eq_zero_iff.mp hor
        rw [modulusScanPrefix_memory, haddr] at hparts
        rw [(ih (by omega)).mp hparts.1]
        have hlast : (loadWord st.memory (count * 32)).toNat = 0 := by
          simpa using congrArg BitVec.toNat hparts.2
        simp [hlast, Nat.mul_comm]
      · intro hlist
        have hparts := List.append_inj hlist (by simp [memoryLimbs])
        apply BitVec.or_eq_zero_iff.mpr
        refine ⟨(ih (by omega)).mpr hparts.1, ?_⟩
        apply BitVec.eq_of_toNat_eq
        rw [modulusScanPrefix_memory, haddr]
        simpa [Nat.mul_comm] using congrArg List.head? hparts.2

theorem modulusOrValue_eq_zero_iff (st : EvmState)
    (modulusSize modOff : U256) (value : Nat)
    (hsize : modulusSize.toNat ≤ 1024)
    (hrep : Represents (BigPath.loadedModulusState st modulusSize modOff).memory
      (0x0000 : Nat) (BigPath.limbCount modulusSize).toNat value) :
    BigPath.modulusOrValue st modulusSize modOff = 0 ↔ value = 0 := by
  rw [BigPath.modulusOrValue, modulusOrPrefix_eq_zero_iff _ _ (by
    simp [BigPath.limbCount, BitVec.toNat_udiv, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega : modulusSize.toNat + 31 <
      115792089237316195423570985008687907853269984665640564039457584007913129639936)]
    omega)]
  constructor
  · intro hzero
    calc
      value = Nat.ofDigits Limbs.radix
          (memoryLimbs (BigPath.loadedModulusState st modulusSize modOff).memory
            0 (BigPath.limbCount modulusSize).toNat) :=
        (value_of_represents hrep).symm
      _ = 0 := by rw [hzero]; simp
  · intro hzero
    subst value
    exact hrep.2.trans (by simp [Limbs.limbDigits, Nat.digitsAppend])

/-! ## Base conversion -/

theorem baseBit_toNat (word : U256) (j : Nat) (hj : j < 8) :
    (BigPath.baseBit word j).toNat = BigFold.msbBit word.toNat j := by
  have hj256 : j < 2 ^ 256 := by omega
  have hshift : (7 - BitVec.ofNat 256 j).toNat = 7 - j := by
    rw [BitVec.toNat_sub_of_le]
    · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj256,
        Nat.mod_eq_of_lt (by omega : j <
          115792089237316195423570985008687907853269984665640564039457584007913129639936)]
    · simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj256]
      omega
  rw [BigPath.baseBit, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    hshift]
  change (word.toNat >>> (7 - j)) &&& 1 = _
  rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rfl

theorem baseBitStep_represents (st : EvmState) (word : U256)
    (j count base modulus : Nat) (hj : j < 8) (hcount : count ≤ 32)
    (hmodulus : 0 < modulus) (hbaseReduced : base < modulus)
    (hbase : Represents st.memory 0x0400 count base)
    (hone : Represents st.memory 0x0c00 count 1)
    (hmod : Represents st.memory 0x0000 count modulus) :
    let after := BigPath.baseBitStep (BitVec.ofNat 256 count) word j st
    Represents after.memory 0x0400 count
        ((2 * base + BigFold.msbBit word.toNat j) % modulus) ∧
      Represents after.memory 0x0c00 count 1 ∧
      Represents after.memory 0x0000 count modulus := by
  let doubled := BigArithmetic.addMaskedModState st 0x0400 0x0400 1 0x0000 count
  let bit := (BigPath.baseBit word j).toNat
  have hbit : BigPath.baseBit word j = BitVec.ofNat 256 bit :=
    (BitVec.eq_of_toNat_eq (by simp [bit])).symm
  have hbitLe : bit ≤ 1 := by
    change (BigPath.baseBit word j).toNat ≤ 1
    rw [baseBit_toNat word j hj]
    have := BigFold.msbBit_lt_two word.toNat j
    omega
  have hdoubledBase : Represents doubled.memory 0x0400 count
      ((base + base) % modulus) := by
    simpa [doubled] using
      addMaskedModState_represents st 0x0400 0x0400 0x0000 count 1
        base base modulus hcount (by omega) hmodulus hbaseReduced
        hbaseReduced.le (by omega) (by omega) (by omega) hbase hbase hmod
        (by left; rfl) (by left; omega) (by left; omega) (by right; omega)
  have hdoubledOne : Represents doubled.memory 0x0c00 count 1 := by
    simpa [doubled] using addMaskedModState_preserves st 0x0400 0x0400
      0x0000 count 1 0x0c00 1 hcount (by omega) (by left; omega)
      (by right; omega) hone
  have hdoubledMod : Represents doubled.memory 0x0000 count modulus := by
    simpa [doubled] using addMaskedModState_preserves st 0x0400 0x0400
      0x0000 count 1 0x0000 modulus hcount (by omega) (by right; omega)
      (by right; omega) hmod
  have hresult : Represents
      (BigArithmetic.addMaskedModState doubled 0x0400 0x0c00
        (BitVec.ofNat 256 bit) 0x0000 count).memory 0x0400 count
      ((((base + base) % modulus) + bit * 1) % modulus) := by
    exact addMaskedModState_represents doubled 0x0400 0x0c00 0x0000 count bit
      ((base + base) % modulus) 1 modulus hcount hbitLe hmodulus
      (Nat.mod_lt _ hmodulus) (by omega) (by omega) (by omega) (by omega)
      hdoubledBase hdoubledOne hdoubledMod (by right; left; omega)
      (by left; omega) (by left; omega) (by right; omega)
  have hresultOne : Represents
      (BigArithmetic.addMaskedModState doubled 0x0400 0x0c00
        (BitVec.ofNat 256 bit) 0x0000 count).memory 0x0c00 count 1 := by
    exact addMaskedModState_preserves doubled 0x0400 0x0c00 0x0000 count bit
      0x0c00 1 hcount (by omega) (by left; omega) (by right; omega)
      hdoubledOne
  have hresultMod : Represents
      (BigArithmetic.addMaskedModState doubled 0x0400 0x0c00
        (BitVec.ofNat 256 bit) 0x0000 count).memory 0x0000 count modulus := by
    exact addMaskedModState_preserves doubled 0x0400 0x0c00 0x0000 count bit
      0x0000 modulus hcount (by omega) (by right; omega) (by right; omega)
      hdoubledMod
  have hvalue : (((base + base) % modulus) + bit * 1) % modulus =
      (2 * base + BigFold.msbBit word.toNat j) % modulus := by
    change (((base + base) % modulus) +
      (BigPath.baseBit word j).toNat * 1) % modulus = _
    rw [baseBit_toNat word j hj, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega
  rw [hvalue] at hresult
  have hn : (BitVec.ofNat 256 count).toNat = count := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show count < 2 ^ 256 by
      exact hcount.trans_lt (by norm_num))]
  simpa [BigPath.baseBitStep, doubled, hn, hbit] using
    And.intro hresult (And.intro hresultOne hresultMod)

theorem baseBitPrefix_represents (st : EvmState) (word : U256)
    (steps count base modulus : Nat) (hsteps : steps ≤ 8)
    (hcount : count ≤ 32) (hmodulus : 0 < modulus)
    (hbaseReduced : base < modulus)
    (hbase : Represents st.memory 0x0400 count base)
    (hone : Represents st.memory 0x0c00 count 1)
    (hmod : Represents st.memory 0x0000 count modulus) :
    let after := BigPath.baseBitPrefix (BitVec.ofNat 256 count) word steps st
    let value := BigFold.hornerBitAfter modulus word.toNat steps base
    Represents after.memory 0x0400 count value ∧
      Represents after.memory 0x0c00 count 1 ∧
      Represents after.memory 0x0000 count modulus := by
  induction steps with
  | zero => simpa [BigPath.baseBitPrefix, BigFold.hornerBitAfter] using
      And.intro hbase (And.intro hone hmod)
  | succ steps ih =>
      have hsteps' : steps ≤ 8 := by omega
      let before := BigPath.baseBitPrefix (BitVec.ofNat 256 count) word steps st
      let beforeValue := BigFold.hornerBitAfter modulus word.toNat steps base
      have hbefore := ih hsteps'
      have hbeforeReduced := BigFold.hornerBitAfter_lt modulus word.toNat steps
        base hmodulus hbaseReduced
      have hstep := baseBitStep_represents before word steps count beforeValue
        modulus (by omega) hcount hmodulus hbeforeReduced hbefore.1
        hbefore.2.1 hbefore.2.2
      simpa [BigPath.baseBitPrefix, BigFold.hornerBitAfter, before,
        beforeValue] using hstep

@[simp] theorem addPhase_calldata (st : EvmState) (dst src mask : U256)
    (steps : Nat) :
    (BigArithmetic.addPhase st dst src mask steps).state.env.calldata =
      st.env.calldata := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigArithmetic.addPhase, BigArithmetic.addStep, ih,
        Challenge.YulProof.EvmState.storeWordAt,
        YulSemantics.EVM.touchMemory]

@[simp] theorem subPhase_calldata (st : EvmState) (dst modulus : U256)
    (steps : Nat) :
    (BigArithmetic.subPhase st dst modulus steps).state.env.calldata =
      st.env.calldata := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigArithmetic.subPhase, BigArithmetic.subStep, ih,
        Challenge.YulProof.EvmState.storeWordAt,
        YulSemantics.EVM.touchMemory]

@[simp] theorem selectPhase_calldata (st : EvmState) (dst mask : U256)
    (steps : Nat) :
    (BigArithmetic.selectPhase st dst mask steps).env.calldata =
      st.env.calldata := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigArithmetic.selectPhase, BigArithmetic.selectStep, ih,
        Challenge.YulProof.EvmState.storeWordAt,
        YulSemantics.EVM.touchMemory]

@[simp] theorem addMaskedModState_calldata (st : EvmState)
    (dst src take modulus : U256) (count : Nat) :
    (BigArithmetic.addMaskedModState st dst src take modulus count).env.calldata =
      st.env.calldata := by
  simp [BigArithmetic.addMaskedModState]

@[simp] theorem baseBitPrefix_calldata (n word : U256) (steps : Nat)
    (st : EvmState) :
    (BigPath.baseBitPrefix n word steps st).env.calldata = st.env.calldata := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigPath.baseBitPrefix, BigPath.baseBitStep, ih]

@[simp] theorem baseBytePrefix_calldata (baseOff n : U256) (steps : Nat)
    (st : EvmState) :
    (BigPath.baseBytePrefix baseOff n steps st).env.calldata =
      st.env.calldata := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigPath.baseBytePrefix, BigPath.baseByteStep, ih]

theorem baseBytePrefix_represents (st : EvmState) (input : ByteArray)
    (baseOff : U256) (steps count base modulus : Nat)
    (hsteps : baseOff.toNat + steps < 2 ^ 256)
    (hcount : count ≤ 32) (hmodulus : 0 < modulus)
    (hbaseReduced : base < modulus)
    (hcalldata : st.env.calldata = input.toList)
    (hbase : Represents st.memory 0x0400 count base)
    (hone : Represents st.memory 0x0c00 count 1)
    (hmod : Represents st.memory 0x0000 count modulus) :
    let after := BigPath.baseBytePrefix baseOff (BitVec.ofNat 256 count)
      steps st
    let value := BigFold.baseByteAfter input baseOff.toNat modulus steps base
    Represents after.memory 0x0400 count value ∧
      Represents after.memory 0x0c00 count 1 ∧
      Represents after.memory 0x0000 count modulus := by
  induction steps with
  | zero => simpa [BigPath.baseBytePrefix, BigFold.baseByteAfter] using
      And.intro hbase (And.intro hone hmod)
  | succ steps ih =>
      let before := BigPath.baseBytePrefix baseOff (BitVec.ofNat 256 count)
        steps st
      let beforeValue := BigFold.baseByteAfter input baseOff.toNat modulus
        steps base
      let address := baseOff + BitVec.ofNat 256 steps
      let word := StateModel.calldataByteValue before address
      have hbefore := ih (by omega)
      have hbeforeReduced := BigFold.baseByteAfter_lt input baseOff.toNat
        modulus steps base hmodulus hbaseReduced
      have hwordByte : word.toNat =
          (byteFrom input.toList (baseOff.toNat + steps)).toNat := by
        have haddress : address.toNat = baseOff.toNat + steps := by
          simp only [address, BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega : steps < 2 ^ 256),
            Nat.mod_eq_of_lt (by omega : baseOff.toNat + steps < 2 ^ 256)]
        rw [WordMath.calldataByteValue_toNat before input address]
        · exact congrArg (fun p => (byteFrom input.toList p).toNat) haddress
        · simpa [before] using hcalldata
      have hbits := baseBitPrefix_represents before word 8 count beforeValue
        modulus (by omega) hcount hmodulus hbeforeReduced hbefore.1
        hbefore.2.1 hbefore.2.2
      dsimp only at hbits
      rw [hwordByte] at hbits
      have hvalue := BigFold.hornerBitAfter_eight modulus word.toNat
        beforeValue hbeforeReduced (by
          rw [hwordByte]
          exact (byteFrom input.toList (baseOff.toNat + steps)).toNat_lt)
      rw [hwordByte] at hvalue
      rw [hvalue] at hbits
      simpa [BigPath.baseBytePrefix, BigPath.baseByteStep, BigFold.baseByteAfter,
        before, beforeValue, address, word] using hbits

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
