import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverBlocks
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.ScheduleCorrect
import Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.MemoryCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Word

namespace Ref
open Challenge.Sha256.Reference.Proofs.Bytecode
abbrev Working := CompressionCorrect.Working
abbrev round := CompressionCorrect.round
abbrev rounds := CompressionCorrect.rounds
abbrev workingOfArray := CompressionCorrect.workingOfArray
abbrev feedForward := CompressionCorrect.feedForward
end Ref

def hOffset (i : Nat) : Nat := 32 + i * 32
def kOffset (i : Nat) : Nat := 2432 + i * 32

def hValue (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (hOffset i)

def kValue (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (kOffset i)

def HashCorrect (memory : ByteArray) (H : Array UInt32) : Prop :=
  ∀ i, i < 8 → hValue memory i = ofUInt32 H[i]!

def ConstantsCorrect (memory : ByteArray) : Prop :=
  ∀ i, i < 64 → kValue memory i = ofUInt32 Sha256.K[i]!

theorem initialized_hash (memory : ByteArray) :
    HashCorrect (DriverBlocks.initializedMemory memory) Sha256.H0 := by
  intro i hi
  interval_cases i <;>
    simp only [hValue, hOffset, DriverBlocks.initializedMemory,
      DriverBlocks.hashMemory, DriverBlocks.constantMemory0,
      DriverBlocks.constantMemory1, DriverBlocks.constantMemory2,
      DriverBlocks.constantMemory3, DriverBlocks.constantMemory4,
      DriverBlocks.constantMemory5, DriverBlocks.constantMemory6,
      DriverBlocks.constantMemory7, Sha256.H0]
  all_goals
    repeat'
      first
      | (rw [Challenge.EvmProof.Memory.readWord_writeWord]; rfl)
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; norm_num)]

theorem initialized_constants (memory : ByteArray) :
    ConstantsCorrect (DriverBlocks.initializedMemory memory) := by
  intro i hi
  interval_cases i <;>
    simp only [kValue, kOffset, DriverBlocks.initializedMemory,
      DriverBlocks.hashMemory, DriverBlocks.constantMemory0,
      DriverBlocks.constantMemory1, DriverBlocks.constantMemory2,
      DriverBlocks.constantMemory3, DriverBlocks.constantMemory4,
      DriverBlocks.constantMemory5, DriverBlocks.constantMemory6,
      DriverBlocks.constantMemory7, Sha256.K]
  all_goals
    repeat'
      first
      | (rw [Challenge.EvmProof.Memory.readWord_writeWord]; rfl)
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; norm_num)]

theorem hash_writeW {memory padded : ByteArray} {blockOff upto : Nat}
    (H : Array UInt32) (h : HashCorrect memory H) :
    HashCorrect
      (ScheduleCorrect.writeW memory upto
        (ScheduleCorrect.scheduleWord padded blockOff upto)) H := by
  intro i hi
  unfold hValue ScheduleCorrect.writeW ScheduleCorrect.wOffset hOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · exact h i hi
  · left; omega

theorem constants_writeW {memory padded : ByteArray} {blockOff upto : Nat}
    (h : ConstantsCorrect memory) (hupto : upto < 64) :
    ConstantsCorrect
      (ScheduleCorrect.writeW memory upto
        (ScheduleCorrect.scheduleWord padded blockOff upto)) := by
  intro i hi
  unfold kValue ScheduleCorrect.writeW ScheduleCorrect.wOffset kOffset
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · exact h i hi
  · right
    simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega

theorem hash_writeFrom {memory padded : ByteArray} {blockOff start : Nat}
    (H : Array UInt32) (h : HashCorrect memory H) :
    ∀ n, HashCorrect
      (ScheduleCorrect.writeFrom memory padded blockOff start n) H := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact hash_writeW H ih

theorem constants_writeFrom {memory padded : ByteArray}
    {blockOff start : Nat} (h : ConstantsCorrect memory)
    (hbound : ∀ n, start + n < 64) :
    ∀ n, ConstantsCorrect
      (ScheduleCorrect.writeFrom memory padded blockOff start n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact constants_writeW ih (hbound n)

theorem hash_writeSchedule (memory padded : ByteArray) (blockOff : Nat)
    (H : Array UInt32) (h : HashCorrect memory H) :
    ∀ n, HashCorrect (ScheduleCorrect.writeSchedule memory padded blockOff n) H := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact hash_writeW H ih

theorem constants_writeSchedule (memory padded : ByteArray) (blockOff : Nat)
    (h : ConstantsCorrect memory) :
    ∀ n, n ≤ 64 → ConstantsCorrect
      (ScheduleCorrect.writeSchedule memory padded blockOff n) := by
  intro n hn
  induction n with
  | zero => exact h
  | succ n ih => exact constants_writeW (ih (by omega)) (by omega)

theorem hash_initialSchedule (memory : ByteArray) (H : Array UInt32)
    (h : HashCorrect memory H) :
    HashCorrect (ScheduleCorrect.initialMemory memory) H := by
  exact hash_writeSchedule memory memory 288 H h 16

theorem constants_initialSchedule (memory : ByteArray)
    (h : ConstantsCorrect memory) :
    ConstantsCorrect (ScheduleCorrect.initialMemory memory) := by
  exact constants_writeSchedule memory memory 288 h 16
    (by omega)

/-- The eight feed-forward stores install `H + working` in the persistent
hash region. -/
theorem folded_hash (memory : ByteArray) (H : Array UInt32) (x : Ref.Working) :
    HashCorrect
      (DriverBlocks.foldedMemory memory
        x.a x.b x.c x.d x.e x.f x.g x.h
        H[0]! H[1]! H[2]! H[3]! H[4]! H[5]! H[6]! H[7]!)
      (Ref.feedForward H x) := by
  intro i hi
  interval_cases i <;>
    simp only [hValue, hOffset, DriverBlocks.foldedMemory]
  all_goals
    repeat'
      first
      | (rw [Challenge.EvmProof.Memory.readWord_writeWord]
         simp only [Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.feedForward]
         ac_rfl)
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; decide)]

theorem folded_constants (memory : ByteArray) (x : Ref.Working)
    (H : Array UInt32) (hK : ConstantsCorrect memory) :
    ConstantsCorrect
      (DriverBlocks.foldedMemory memory
        x.a x.b x.c x.d x.e x.f x.g x.h
        H[0]! H[1]! H[2]! H[3]! H[4]! H[5]! H[6]! H[7]!) := by
  intro i hi
  unfold kValue kOffset DriverBlocks.foldedMemory
  repeat'
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; right; omega)]
  exact hK i hi

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.MemoryCorrect
