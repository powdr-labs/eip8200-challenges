import Challenge.EvmProof.Memory

set_option warningAsError true

/-!
# Typed EVM memory regions

Small interval and representation combinators over byte-array memory. These
hide pointwise read/write details from cryptographic structure proofs.
-/

namespace Challenge.EvmProof.MemoryRegion

open EvmSemantics

structure Region where
  start : Nat
  size : Nat
deriving DecidableEq, Repr

def Region.stop (region : Region) : Nat := region.start + region.size

def Disjoint (left right : Region) : Prop :=
  left.stop ≤ right.start ∨ right.stop ≤ left.start

def read (memory : ByteArray) (region : Region) : ByteArray :=
  MachineState.readPadded memory region.start region.size

def write (memory : ByteArray) (region : Region) (bytes : ByteArray) : ByteArray :=
  MachineState.writeBytes memory bytes region.start

def Represents (memory : ByteArray) (region : Region) (bytes : ByteArray) : Prop :=
  bytes.size = region.size ∧ read memory region = bytes

def wordSlot (base index : Nat) : Region :=
  { start := base + 32 * index, size := 32 }

theorem disjoint_symm {left right : Region} (h : Disjoint left right) :
    Disjoint right left := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

@[simp] theorem read_size (memory : ByteArray) (region : Region) :
    (read memory region).size = region.size := by
  exact Challenge.EvmProof.Memory.readPadded_size _ _ _

theorem read_write_same (memory bytes : ByteArray) (region : Region)
    (hsize : bytes.size = region.size) :
    read (write memory region bytes) region = bytes := by
  unfold read write
  rw [← hsize]
  exact Challenge.EvmProof.Memory.readPadded_writeBytes_same _ _ _

theorem read_write_disjoint (memory bytes : ByteArray) (readRegion writeRegion : Region)
    (hsize : bytes.size = writeRegion.size)
    (hdisjoint : Disjoint readRegion writeRegion) :
    read (write memory writeRegion bytes) readRegion = read memory readRegion := by
  unfold read write
  apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
  simpa [Disjoint, Region.stop, hsize] using hdisjoint

theorem represents_write_same (memory bytes : ByteArray) (region : Region)
    (hsize : bytes.size = region.size) :
    Represents (write memory region bytes) region bytes := by
  exact ⟨hsize, read_write_same memory bytes region hsize⟩

theorem represents_write_disjoint {memory bytes value : ByteArray}
    {represented written : Region}
    (hrep : Represents memory represented value)
    (hsize : bytes.size = written.size)
    (hdisjoint : Disjoint represented written) :
    Represents (write memory written bytes) represented value := by
  refine ⟨hrep.1, ?_⟩
  rw [read_write_disjoint memory bytes represented written hsize hdisjoint]
  exact hrep.2

theorem wordSlots_disjoint (base i j : Nat) (hij : i ≠ j) :
    Disjoint (wordSlot base i) (wordSlot base j) := by
  unfold Disjoint Region.stop wordSlot
  simp only
  omega

end Challenge.EvmProof.MemoryRegion

