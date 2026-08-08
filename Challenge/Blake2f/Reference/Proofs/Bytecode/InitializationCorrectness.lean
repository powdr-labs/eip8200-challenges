import Challenge.Blake2f.ProofSupport.Input
import Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness

set_option warningAsError true

/-! Functional model of the memory produced by the compiled input decoder. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.InitializationCorrectness

open Challenge.Blake2f
open Challenge.Blake2f.ProofSupport
open EvmSemantics

theorem decodedWord_eq (input : ByteArray) (offset : Nat) :
    Initialization.decodedWord input offset =
      Word.ofUInt64 (Crypto.Blake2f.readLE64 input offset) := by
  exact LoadLE64.accumulator_eight_eq_readLE64 input offset

@[simp] theorem initialization_storeWord_eq (memory : ByteArray) (offset : Nat)
    (value : UInt256) :
    Initialization.storeWord memory offset value =
      Memory.storeWord memory offset value := rfl

theorem decodeWords_represents (input : ByteArray) (calldataBase memoryBase count : Nat)
    (initial : ByteArray) :
    Memory.RepresentsAt
      (Initialization.decodeWords input calldataBase memoryBase count initial)
      memoryBase (Input.readWords input calldataBase count) := by
  induction count with
  | zero =>
      intro i hi
      simp [Input.readWords] at hi
  | succ count ih =>
      rw [Initialization.decodeWords, Input.readWords_succ]
      simpa [Initialization.storeWord, Memory.storeWord, decodedWord_eq,
        Input.readWords, Nat.mul_comm] using
        Memory.representsAt_storeWord_push
          (Crypto.Blake2f.readLE64 input (calldataBase + count * 8)) ih

theorem decodeWords_preserves_before (input : ByteArray)
    (calldataBase memoryBase count : Nat) (initial : ByteArray)
    {base : Nat} {values : Array UInt64}
    (represents : Memory.RepresentsAt initial base values)
    (hbefore : base + 32 * values.size ≤ memoryBase) :
    Memory.RepresentsAt
      (Initialization.decodeWords input calldataBase memoryBase count initial)
      base values := by
  induction count with
  | zero => exact represents
  | succ count ih =>
      rw [Initialization.decodeWords]
      apply Memory.representsAt_storeWord_disjoint
      · exact ih
      · intro i hi
        unfold Memory.WordDisjoint
        left
        omega

theorem hMemory_represents (input : ByteArray) :
    Memory.RepresentsAt (Initialization.hMemory input 8) 0
      (Input.chaining input) := by
  simpa [Initialization.hMemory, Input.chaining] using
    decodeWords_represents input 4 0 8 ByteArray.empty

theorem mMemory_represents_h (input : ByteArray) :
    Memory.RepresentsAt (Initialization.mMemory input) 0
      (Input.chaining input) := by
  apply decodeWords_preserves_before
  · exact hMemory_represents input
  · simp

theorem mMemory_represents_message (input : ByteArray) :
    Memory.RepresentsAt (Initialization.mMemory input) 256
      (Input.message input) := by
  simpa [Initialization.mMemory, Input.message] using
    decodeWords_represents input 68 256 16 (Initialization.hMemory input 8)

/-- Copying the chaining state into the work-vector area cannot change a
word ending before that area. -/
theorem readWord_copyHToV_before (count : Nat) (memory : ByteArray)
    (offset : Nat) (hbefore : offset + 32 ≤ 768) :
    MachineState.readWord (Initialization.copyHToV count memory) offset =
      MachineState.readWord memory offset := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Initialization.copyHToV]
      rw [RoundCorrectness.readWord_initialization_storeWord_disjoint]
      · exact ih
      · exact Or.inl (by omega)

/-- Every copied work-vector lane is the corresponding source lane. -/
theorem readWord_copyHToV_target (count : Nat) (memory : ByteArray) (i : Nat)
    (hcount : count ≤ 8) (hi : i < count) :
    MachineState.readWord (Initialization.copyHToV count memory)
        (768 + 32 * i) =
      MachineState.readWord memory (32 * i) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [Initialization.copyHToV]
      by_cases hlast : i = count
      · subst i
        rw [RoundCorrectness.readWord_initialization_storeWord_same]
        exact readWord_copyHToV_before count memory (32 * count) (by omega)
      · rw [RoundCorrectness.readWord_initialization_storeWord_disjoint]
        · exact ih (by omega) (by omega)
        · exact Memory.wordDisjoint_slots 768 i count hlast

theorem vMemory_represents_h (input : ByteArray) (count : Nat) :
    Memory.RepresentsAt (Initialization.vMemory input count) 0
      (Input.chaining input) := by
  intro i hi
  simp only [Nat.zero_add]
  rw [Initialization.vMemory,
    readWord_copyHToV_before count (Initialization.mMemory input) (32 * i)
      (by have := Input.chaining_size input; omega)]
  simpa using mMemory_represents_h input i hi

theorem vMemory_represents_message (input : ByteArray) (count : Nat) :
    Memory.RepresentsAt (Initialization.vMemory input count) 256
      (Input.message input) := by
  intro i hi
  rw [Initialization.vMemory,
    readWord_copyHToV_before count (Initialization.mMemory input) (256 + 32 * i)
      (by have := Input.message_size input; omega)]
  exact mMemory_represents_message input i hi

theorem vMemory_represents_vector (input : ByteArray) :
    Memory.RepresentsAt (Initialization.vMemory input 8) 768
      (Input.chaining input) := by
  intro i hi
  rw [Initialization.vMemory,
    readWord_copyHToV_target 8 (Initialization.mMemory input) i (by omega) (by
      have := Input.chaining_size input
      omega)]
  simpa using mMemory_represents_h input i hi

private theorem foldl_fixedStores_preserves {memory : ByteArray}
    {base : Nat} {values : Array UInt64} (entries : List (Nat × Nat))
    (hdisjoint : ∀ entry ∈ entries, ∀ i, i < values.size →
      Memory.WordDisjoint (base + 32 * i) entry.1)
    (represents : Memory.RepresentsAt memory base values) :
    Memory.RepresentsAt
      (entries.foldl Initialization.applyFixedStore memory) base values := by
  induction entries generalizing memory with
  | nil => exact represents
  | cons entry entries ih =>
      rw [List.foldl_cons]
      apply ih
      · intro later hlater i hi
        exact hdisjoint later (List.mem_cons_of_mem entry hlater) i hi
      · simpa only [Initialization.applyFixedStore,
          initialization_storeWord_eq] using
          Memory.representsAt_storeWord_disjoint
            (UInt256.ofNat entry.2) represents
            (fun i hi => hdisjoint entry (by simp) i hi)

theorem constantsMemory_represents_h (input : ByteArray) :
    Memory.RepresentsAt (Initialization.constantsMemory input) 0
      (Input.chaining input) := by
  rw [Initialization.constantsMemory]
  apply foldl_fixedStores_preserves Initialization.fixedStores
  · intro entry hentry i hi
    have hstart : 1024 ≤ entry.1 := by
      simp [Initialization.fixedStores] at hentry
      rcases hentry with hentry | hentry | hentry | hentry | hentry |
          hentry | hentry | hentry | hentry | hentry | hentry | hentry |
          hentry | hentry | hentry | hentry | hentry | hentry <;> simp_all
    exact Or.inl (by
      have := Input.chaining_size input
      omega)
  · exact vMemory_represents_h input 8

theorem constantsMemory_represents_message (input : ByteArray) :
    Memory.RepresentsAt (Initialization.constantsMemory input) 256
      (Input.message input) := by
  rw [Initialization.constantsMemory]
  apply foldl_fixedStores_preserves Initialization.fixedStores
  · intro entry hentry i hi
    have hstart : 1024 ≤ entry.1 := by
      simp [Initialization.fixedStores] at hentry
      rcases hentry with hentry | hentry | hentry | hentry | hentry |
          hentry | hentry | hentry | hentry | hentry | hentry | hentry |
          hentry | hentry | hentry | hentry | hentry | hentry <;> simp_all
    exact Or.inl (by
      have := Input.message_size input
      omega)
  · exact vMemory_represents_message input 8

private def unmodifiedVector (h : Array UInt64) : Array UInt64 :=
  ((((((((h.push 0x6a09e667f3bcc908).push 0xbb67ae8584caa73b).push
    0x3c6ef372fe94f82b).push 0xa54ff53a5f1d36f1).push
    0x510e527fade682d1).push 0x9b05688c2b3e6c1f).push
    0x1f83d9abfb41bd6b).push 0x5be0cd19137e2179)

private theorem initialVector_zero_eq (h : Array UInt64) (hsize : h.size = 8) :
    Algorithm.initialVector h 0 0 false = unmodifiedVector h := by
  simp only [Algorithm.initialVector, Crypto.Blake2f.IV,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl]
  norm_num [List.range', List.range.loop, unmodifiedVector]
  have hexplicit : h = #[h[0]!, h[1]!, h[2]!, h[3]!,
      h[4]!, h[5]!, h[6]!, h[7]!] := by
    apply Array.ext
    · simp [hsize]
    · intro i hleft hright
      have hi : i < 8 := by simpa using hright
      interval_cases i <;> simp <;>
        exact (getElem!_pos h _ (by omega)).symm
  rw [hexplicit]
  simp

private def ivStores : List (Nat × Nat) :=
  [(1024, 0x6a09e667f3bcc908),
   (1056, 0xbb67ae8584caa73b),
   (1088, 0x3c6ef372fe94f82b),
   (1120, 0xa54ff53a5f1d36f1),
   (1152, 0x510e527fade682d1),
   (1184, 0x9b05688c2b3e6c1f),
   (1216, 0x1f83d9abfb41bd6b),
   (1248, 0x5be0cd19137e2179)]

private def ivWords : List UInt64 :=
  [0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
   0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
   0x510e527fade682d1, 0x9b05688c2b3e6c1f,
   0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

private def sigmaStores : List (Nat × Nat) :=
  [(1536, 0x000102030405060708090a0b0c0d0e0f),
   (1568, 0x0e0a0408090f0d06010c00020b070503),
   (1600, 0x0b080c0005020f0d0a0e030607010904),
   (1632, 0x070903010d0c0b0e0206050a04000f08),
   (1664, 0x0900050702040a0f0e010b0c0608030d),
   (1696, 0x020c060a000b0803040d07050f0e0109),
   (1728, 0x0c05010f0e0d040a000706030902080b),
   (1760, 0x0d0b070e0c01030905000f040806020a),
   (1792, 0x060f0e090b0300080c020d0701040a05),
   (1824, 0x0a020804070601050f0b090e030c0d00)]

private theorem fixedStores_eq :
    Initialization.fixedStores = ivStores ++ sigmaStores := by
  rfl

theorem constantsMemory_represents_vector (input : ByteArray) :
    Memory.RepresentsAt (Initialization.constantsMemory input) 768
      (Algorithm.initialVector (Input.chaining input) 0 0 false) := by
  rw [initialVector_zero_eq _ (Input.chaining_size input)]
  have appended := Memory.representsAt_appendStoreWords ivWords
    (vMemory_represents_vector input)
  have hw0 : UInt256.ofNat 0x6a09e667f3bcc908 =
      Word.ofUInt64 0x6a09e667f3bcc908 := by decide
  have hw1 : UInt256.ofNat 0xbb67ae8584caa73b =
      Word.ofUInt64 0xbb67ae8584caa73b := by decide
  have hw2 : UInt256.ofNat 0x3c6ef372fe94f82b =
      Word.ofUInt64 0x3c6ef372fe94f82b := by decide
  have hw3 : UInt256.ofNat 0xa54ff53a5f1d36f1 =
      Word.ofUInt64 0xa54ff53a5f1d36f1 := by decide
  have hw4 : UInt256.ofNat 0x510e527fade682d1 =
      Word.ofUInt64 0x510e527fade682d1 := by decide
  have hw5 : UInt256.ofNat 0x9b05688c2b3e6c1f =
      Word.ofUInt64 0x9b05688c2b3e6c1f := by decide
  have hw6 : UInt256.ofNat 0x1f83d9abfb41bd6b =
      Word.ofUInt64 0x1f83d9abfb41bd6b := by decide
  have hw7 : UInt256.ofNat 0x5be0cd19137e2179 =
      Word.ofUInt64 0x5be0cd19137e2179 := by decide
  have hmemory :
      ivStores.foldl Initialization.applyFixedStore
          (Initialization.vMemory input 8) =
        Memory.appendStoreWords (Initialization.vMemory input 8) 768
          (Input.chaining input) ivWords := by
    simp only [ivStores, ivWords, Initialization.applyFixedStore,
      initialization_storeWord_eq, List.foldl_cons, List.foldl_nil,
      Memory.appendStoreWords,
      Input.chaining_size, Array.size_push, hw0, hw1, hw2, hw3, hw4, hw5,
      hw6, hw7, Nat.reduceAdd, Nat.reduceMul]
  have hvalues :
      Memory.appendValues (Input.chaining input) ivWords =
        unmodifiedVector (Input.chaining input) := by
    rfl
  have repIv : Memory.RepresentsAt
      (ivStores.foldl Initialization.applyFixedStore
        (Initialization.vMemory input 8)) 768
      (unmodifiedVector (Input.chaining input)) := by
    rw [hmemory, ← hvalues]
    exact appended
  rw [Initialization.constantsMemory, fixedStores_eq, List.foldl_append]
  apply foldl_fixedStores_preserves sigmaStores
  · intro entry hentry i hi
    have hstart : 1536 ≤ entry.1 := by
      simp [sigmaStores] at hentry
      rcases hentry with hentry | hentry | hentry | hentry | hentry |
          hentry | hentry | hentry | hentry | hentry <;> simp_all
    exact Or.inl (by
      have : i < 16 := by simpa [unmodifiedVector] using hi
      omega)
  · exact repIv

end Challenge.Blake2f.Reference.Proofs.Bytecode.InitializationCorrectness
