import Challenge.Blake2f.ProofSupport.Algorithm
import Challenge.EvmProof.Memory

set_option warningAsError true

/-!
# Reusable word-oriented memory view

BLAKE2f bytecodes commonly keep each 64-bit lane in a full EVM memory word.
These definitions hide the byte-array encoding and provide the same/disjoint
read lemmas needed to relate such layouts to the pure algorithm model.
-/

namespace Challenge.Blake2f.ProofSupport.Memory

open EvmSemantics

def storeWord (memory : ByteArray) (offset : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

def WordDisjoint (a b : Nat) : Prop := a + 32 ≤ b ∨ b + 32 ≤ a

theorem WordDisjoint.symm {a b : Nat} (h : WordDisjoint a b) :
    WordDisjoint b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

@[simp] theorem readWord_storeWord_same (memory : ByteArray) (offset : Nat)
    (value : UInt256) :
    MachineState.readWord (storeWord memory offset value) offset = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset value

theorem readWord_storeWord_disjoint (memory : ByteArray) (readStart writeStart : Nat)
    (value : UInt256) (h : WordDisjoint readStart writeStart) :
    MachineState.readWord (storeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa [WordDisjoint, Data.Bytes.natToBytesPadded, ByteArray.size] using h

/-- Four word-aligned lanes projected from arbitrary byte-array memory. -/
def lanesAtWords (memory : ByteArray) (a b c d : Nat) :
    Algorithm.Lanes UInt256 :=
  ⟨MachineState.readWord memory a, MachineState.readWord memory b,
    MachineState.readWord memory c, MachineState.readWord memory d⟩

/-- A 64-bit array represented by consecutive 32-byte EVM words. -/
def RepresentsAt (memory : ByteArray) (base : Nat) (values : Array UInt64) : Prop :=
  ∀ i, i < values.size →
    MachineState.readWord memory (base + 32 * i) =
      Word.ofUInt64 values[i]!

/-- Distinct slots in the consecutive 32-byte layout never overlap. -/
theorem wordDisjoint_slots (base i j : Nat) (hij : i ≠ j) :
    WordDisjoint (base + 32 * i) (base + 32 * j) := by
  unfold WordDisjoint
  omega

/-- Projecting represented slots produces the embedded algorithm lanes. -/
theorem lanesAtWords_of_representsAt {memory : ByteArray} {base : Nat}
    {values : Array UInt64} (represents : RepresentsAt memory base values)
    (a b c d : Nat) (ha : a < values.size) (hb : b < values.size)
    (hc : c < values.size) (hd : d < values.size) :
    lanesAtWords memory (base + 32 * a) (base + 32 * b)
        (base + 32 * c) (base + 32 * d) =
      (Algorithm.lanesAt values a b c d).embed := by
  apply Algorithm.Lanes.ext <;>
    simp only [lanesAtWords, Algorithm.lanesAt, Algorithm.Lanes.embed]
  · exact represents a ha
  · exact represents b hb
  · exact represents c hc
  · exact represents d hd

/-- Extend a represented consecutive array by storing its next embedded
64-bit word. This is the standard invariant step for decoding loops. -/
theorem representsAt_storeWord_push {memory : ByteArray} {base : Nat}
    {values : Array UInt64} (value : UInt64)
    (represents : RepresentsAt memory base values) :
    RepresentsAt
      (storeWord memory (base + 32 * values.size) (Word.ofUInt64 value)) base
      (values.push value) := by
  intro i hi
  rw [Array.size_push] at hi
  by_cases hlast : i = values.size
  · subst i
    simp
  · have hiold : i < values.size := by omega
    rw [readWord_storeWord_disjoint memory (base + 32 * i)
      (base + 32 * values.size) (Word.ofUInt64 value)
      (wordDisjoint_slots base i values.size hlast)]
    rw [represents i hiold]
    congr 1
    rw [getElem!_pos values i hiold,
      getElem!_pos (values.push value) i (by simp; omega)]
    exact (Array.getElem_push_lt hiold).symm

/-- Pure value companion for a sequence of consecutive word stores. -/
def appendValues (values : Array UInt64) : List UInt64 → Array UInt64
  | [] => values
  | value :: rest => appendValues (values.push value) rest

/-- Append embedded 64-bit words immediately after an already represented
array. Keeping this operation opaque prevents concrete proofs from expanding
nested byte-array writes. -/
def appendStoreWords (memory : ByteArray) (base : Nat)
    (values : Array UInt64) : List UInt64 → ByteArray
  | [] => memory
  | value :: rest =>
      appendStoreWords
        (storeWord memory (base + 32 * values.size) (Word.ofUInt64 value))
        base (values.push value) rest

theorem representsAt_appendStoreWords {memory : ByteArray} {base : Nat}
    {values : Array UInt64} (words : List UInt64)
    (represents : RepresentsAt memory base values) :
    RepresentsAt (appendStoreWords memory base values words) base
      (appendValues values words) := by
  induction words generalizing memory values with
  | nil => exact represents
  | cons value words ih =>
      rw [appendStoreWords, appendValues]
      exact ih (representsAt_storeWord_push value represents)

/-- Update one represented lane with another embedded 64-bit value. -/
theorem representsAt_storeWord_set {memory : ByteArray} {base : Nat}
    {values : Array UInt64} (index : Nat) (value : UInt64)
    (hi : index < values.size) (represents : RepresentsAt memory base values) :
    RepresentsAt
      (storeWord memory (base + 32 * index) (Word.ofUInt64 value)) base
      (values.set! index value) := by
  intro i hnew
  have hold : i < values.size := by
    simpa [Array.set!_eq_setIfInBounds] using hnew
  by_cases hsame : index = i
  · subst i
    rw [readWord_storeWord_same]
    simp [Array.set!_eq_setIfInBounds, hi]
  · rw [readWord_storeWord_disjoint memory (base + 32 * i)
      (base + 32 * index) (Word.ofUInt64 value)
      (wordDisjoint_slots base i index (Ne.symm hsame))]
    rw [represents i hold]
    congr 1
    exact (Algorithm.getElem!_set!_other values index i value hold hsame).symm

/-- A store outside every represented slot preserves the represented array. -/
theorem representsAt_storeWord_disjoint {memory : ByteArray} {base offset : Nat}
    {values : Array UInt64} (value : UInt256)
    (represents : RepresentsAt memory base values)
    (hdisjoint : ∀ i, i < values.size →
      WordDisjoint (base + 32 * i) offset) :
    RepresentsAt (storeWord memory offset value) base values := by
  intro i hi
  rw [readWord_storeWord_disjoint memory (base + 32 * i) offset value
    (hdisjoint i hi)]
  exact represents i hi

end Challenge.Blake2f.ProofSupport.Memory
