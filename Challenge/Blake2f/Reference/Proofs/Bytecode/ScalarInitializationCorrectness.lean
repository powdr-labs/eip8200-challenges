import Challenge.Blake2f.Reference.Proofs.Bytecode.InitializationCorrectness

set_option warningAsError true
set_option maxHeartbeats 1000000

/-! Functional refinement of the compiled counter and final-flag stores. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitializationCorrectness

open Challenge.Blake2f
open Challenge.Blake2f.ProofSupport
open EvmSemantics

private theorem xor_eq (x y : UInt256) : UInt256.xor x y = x ^^^ y := rfl

def t0Vector (input : ByteArray) : Array UInt64 :=
  let v := Algorithm.initialVector (Input.chaining input) 0 0 false
  v.set! 12 (v[12]! ^^^ Input.t0 input)

theorem t0Memory_represents_vector (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.t0Memory input) 768
      (t0Vector input) := by
  have rep := InitializationCorrectness.constantsMemory_represents_vector input
  have h12 := rep 12 (by simp)
  have updated := Memory.representsAt_storeWord_set 12
    ((Algorithm.initialVector (Input.chaining input) 0 0 false)[12]! ^^^
      Input.t0 input) (by simp) rep
  unfold ScalarInitialization.t0Memory
  rw [InitializationCorrectness.initialization_storeWord_eq, h12,
    ScalarInitialization.t0Word, InitializationCorrectness.decodedWord_eq]
  rw [show Crypto.Blake2f.readLE64 input 196 = Input.t0 input by rfl,
    xor_eq, ← Word.ofUInt64_xor]
  simpa only [t0Vector] using updated

theorem t1Memory_represents_vector (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.t1Memory input) 768
      (Algorithm.counterVector (Input.chaining input)
        (Input.t0 input) (Input.t1 input)) := by
  have rep := t0Memory_represents_vector input
  have h13 := rep 13 (by simp [t0Vector])
  have updated := Memory.representsAt_storeWord_set 13
    ((t0Vector input)[13]! ^^^ Input.t1 input) (by simp [t0Vector]) rep
  unfold ScalarInitialization.t1Memory
  rw [InitializationCorrectness.initialization_storeWord_eq, h13,
    ScalarInitialization.t1Word, InitializationCorrectness.decodedWord_eq]
  rw [show Crypto.Blake2f.readLE64 input 204 = Input.t1 input by rfl,
    xor_eq, ← Word.ofUInt64_xor]
  simpa only [Algorithm.counterVector, t0Vector] using updated

theorem flaggedMemory_represents_vector (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.flaggedMemory input) 768
      (Algorithm.flaggedVector (Input.chaining input)
        (Input.t0 input) (Input.t1 input)) := by
  have rep := t1Memory_represents_vector input
  have h14 := rep 14 (by simp [Algorithm.counterVector])
  have updated := Memory.representsAt_storeWord_set 14
    ((Algorithm.counterVector (Input.chaining input)
      (Input.t0 input) (Input.t1 input))[14]! ^^^ 0xffffffffffffffff)
    (by simp [Algorithm.counterVector]) rep
  unfold ScalarInitialization.flaggedMemory
  rw [InitializationCorrectness.initialization_storeWord_eq, h14]
  have hmask : UInt256.ofNat 0xffffffffffffffff =
      Word.ofUInt64 0xffffffffffffffff := by decide
  rw [hmask, xor_eq, ← Word.ofUInt64_xor]
  simpa only [Algorithm.flaggedVector] using updated

private theorem scalarStore_preserves {memory : ByteArray} {base : Nat}
    {values : Array UInt64} (offset : Nat) (value : UInt256)
    (represents : Memory.RepresentsAt memory base values)
    (hbefore : base + 32 * values.size ≤ offset) :
    Memory.RepresentsAt (Initialization.storeWord memory offset value)
      base values := by
  rw [InitializationCorrectness.initialization_storeWord_eq]
  apply Memory.representsAt_storeWord_disjoint value represents
  intro i hi
  exact Or.inl (by omega)

theorem t1Memory_represents_h (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.t1Memory input) 0
      (Input.chaining input) := by
  unfold ScalarInitialization.t1Memory ScalarInitialization.t0Memory
  apply scalarStore_preserves
  · apply scalarStore_preserves
    · exact InitializationCorrectness.constantsMemory_represents_h input
    · simp
  · simp

theorem t1Memory_represents_message (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.t1Memory input) 256
      (Input.message input) := by
  unfold ScalarInitialization.t1Memory ScalarInitialization.t0Memory
  apply scalarStore_preserves
  · apply scalarStore_preserves
    · exact InitializationCorrectness.constantsMemory_represents_message input
    · simp
  · simp

theorem flaggedMemory_represents_h (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.flaggedMemory input) 0
      (Input.chaining input) := by
  unfold ScalarInitialization.flaggedMemory
  apply scalarStore_preserves
  · exact t1Memory_represents_h input
  · simp

theorem flaggedMemory_represents_message (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.flaggedMemory input) 256
      (Input.message input) := by
  unfold ScalarInitialization.flaggedMemory
  apply scalarStore_preserves
  · exact t1Memory_represents_message input
  · simp

theorem finalMemory_represents_h (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.finalMemory input) 0
      (Input.chaining input) := by
  unfold ScalarInitialization.finalMemory
  split
  · exact t1Memory_represents_h input
  · exact flaggedMemory_represents_h input

theorem finalMemory_represents_message (input : ByteArray) :
    Memory.RepresentsAt (ScalarInitialization.finalMemory input) 256
      (Input.message input) := by
  unfold ScalarInitialization.finalMemory
  split
  · exact t1Memory_represents_message input
  · exact flaggedMemory_represents_message input

theorem finalMemory_represents_vector (input : ByteArray)
    (hflag : input[212]!.toNat ≤ 1) :
    Memory.RepresentsAt (ScalarInitialization.finalMemory input) 768
      (Algorithm.initialVector (Input.chaining input) (Input.t0 input)
        (Input.t1 input) (Input.finalFlag input)) := by
  by_cases hzero : input[212]!.toNat = 0
  · have hbyte : input[212]! = 0 := UInt8.toNat_inj.mp (by simpa using hzero)
    rw [ScalarInitialization.finalMemory, if_pos hzero]
    simpa [Input.finalFlag, hbyte, Algorithm.counterVector_eq] using
      t1Memory_represents_vector input
  · have hone : input[212]!.toNat = 1 := by omega
    have hbyte : input[212]! = 1 := UInt8.toNat_inj.mp (by simpa using hone)
    rw [ScalarInitialization.finalMemory, if_neg hzero]
    simpa [Input.finalFlag, hbyte, Algorithm.flaggedVector_eq] using
      flaggedMemory_represents_vector input

theorem finalMemory_model (input : ByteArray)
    (hflag : input[212]!.toNat ≤ 1) :
    RoundCorrectness.MemoryModel (ScalarInitialization.finalMemory input)
      (Input.message input)
      (Algorithm.initialVector (Input.chaining input) (Input.t0 input)
        (Input.t1 input) (Input.finalFlag input)) :=
  ⟨RoundCorrectness.schedule_finalMemory input,
    finalMemory_represents_message input,
    finalMemory_represents_vector input hflag⟩

end Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitializationCorrectness
