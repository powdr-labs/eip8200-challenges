import Challenge.Blake2f.Reference.Proofs.Bytecode.RoundGas

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Memory invariants connecting compiled rounds to the pure BLAKE2f model. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness

open Challenge.Blake2f
open Challenge.Blake2f.ProofSupport
open EvmSemantics

def sigmaPacked : Nat → Nat
  | 0 => 0x000102030405060708090a0b0c0d0e0f
  | 1 => 0x0e0a0408090f0d06010c00020b070503
  | 2 => 0x0b080c0005020f0d0a0e030607010904
  | 3 => 0x070903010d0c0b0e0206050a04000f08
  | 4 => 0x0900050702040a0f0e010b0c0608030d
  | 5 => 0x020c060a000b0803040d07050f0e0109
  | 6 => 0x0c05010f0e0d040a000706030902080b
  | 7 => 0x0d0b070e0c01030905000f040806020a
  | 8 => 0x060f0e090b0300080c020d0701040a05
  | _ => 0x0a020804070601050f0b090e030c0d00

def ScheduleRows (memory : ByteArray) : Prop :=
  ∀ round : UInt256, MixG.rowWord memory round =
    UInt256.ofNat (sigmaPacked (round.toNat % 10))

theorem rowOffset_toNat_word (round : UInt256) :
    (MixG.rowOffset round).toNat = 1536 + 32 * (round.toNat % 10) := by
  have hmod : round.toNat % 10 < 10 := Nat.mod_lt _ (by omega)
  have hwordMod : round % UInt256.ofNat 10 =
      UInt256.ofNat (round.toNat % 10) := by
    apply Challenge.EvmProof.Word.word_ext
    change (UInt256.mod round (UInt256.ofNat 10)).toNat =
      (UInt256.ofNat (round.toNat % 10)).toNat
    unfold UInt256.mod
    rw [if_neg (by decide)]
    change round.toNat % (10 % 2 ^ 256) =
      (round.toNat % 10) % 2 ^ 256
    rw [Nat.mod_eq_of_lt (by norm_num : 10 < 2 ^ 256),
      Nat.mod_eq_of_lt (Nat.lt_trans hmod (by norm_num))]
  have hshift : UInt256.shiftLeft (UInt256.ofNat (round.toNat % 10))
      (UInt256.ofNat 5) = UInt256.ofNat ((round.toNat % 10) * 2 ^ 5) :=
    Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by omega)
  have hadd : UInt256.ofNat 1536 + UInt256.ofNat ((round.toNat % 10) * 2 ^ 5) =
      UInt256.ofNat (1536 + (round.toNat % 10) * 2 ^ 5) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  rw [MixG.rowOffset, hwordMod, hshift, hadd,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem rowOffset_toNat (round : Nat) (hround : round < 2 ^ 256) :
    (MixG.rowOffset (UInt256.ofNat round)).toNat =
      1536 + 32 * (round % 10) := by
  rw [rowOffset_toNat_word, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hround]

theorem accessSafe_of_schedule {memory : ByteArray} (round : Nat)
    (hround : round < 2 ^ 256) (schedule : ScheduleRows memory) :
    Round.AccessSafe memory round := by
  constructor
  · rw [rowOffset_toNat round hround]
    have hm : round % 10 < 10 := Nat.mod_lt _ (by omega)
    omega
  · intro column hcolumn
    have hrow := schedule (UInt256.ofNat round)
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hround] at hrow
    rw [hrow]
    have hm : round % 10 < 10 := Nat.mod_lt _ (by omega)
    interval_cases hr : round % 10 <;>
      interval_cases hc : column <;>
      subst_vars <;>
      norm_num [MixG.messageOffset, sigmaPacked, UInt256.byteAt,
        UInt256.shiftLeft, UInt256.add,
        Challenge.EvmProof.Word.ofNat_add_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat] at * <;>
      decide

/-- A compiled quarter-round cannot modify the sigma table when all four of
its scratch lanes end before the table begins. -/
theorem schedule_transition {memory : ByteArray}
    (a b c d round xColumn yColumn : UInt256)
    (schedule : ScheduleRows memory)
    (ha : a.toNat + 32 ≤ 1536) (hb : b.toNat + 32 ≤ 1536)
    (hc : c.toNat + 32 ≤ 1536) (hd : d.toNat + 32 ≤ 1536) :
    ScheduleRows (MixG.transition memory a b c d round xColumn yColumn) := by
  intro selectedRound
  unfold MixG.rowWord
  rw [MixGCorrectness.readWord_transition_disjoint]
  · exact schedule selectedRound
  all_goals
    rw [rowOffset_toNat_word]
    exact Or.inr (by omega)

theorem schedule_memory1 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory1 memory round) := by
  apply schedule_transition
  · exact schedule
  all_goals decide

theorem schedule_memory2 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory2 memory round) := by
  apply schedule_transition
  · exact schedule_memory1 round schedule
  all_goals decide

theorem schedule_memory3 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory3 memory round) := by
  apply schedule_transition
  · exact schedule_memory2 round schedule
  all_goals decide

theorem schedule_memory4 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory4 memory round) := by
  apply schedule_transition
  · exact schedule_memory3 round schedule
  all_goals decide

theorem schedule_memory5 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory5 memory round) := by
  apply schedule_transition
  · exact schedule_memory4 round schedule
  all_goals decide

theorem schedule_memory6 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory6 memory round) := by
  apply schedule_transition
  · exact schedule_memory5 round schedule
  all_goals decide

theorem schedule_memory7 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory7 memory round) := by
  apply schedule_transition
  · exact schedule_memory6 round schedule
  all_goals decide

theorem schedule_transition_round {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.transition memory round) := by
  apply schedule_transition
  · exact schedule_memory7 round schedule
  all_goals decide

theorem iterationSafe_of_schedule {memory : ByteArray} (round : Nat)
    (hround : round < 2 ^ 256) (schedule : ScheduleRows memory) :
    Round.IterationSafe memory round := by
  exact ⟨accessSafe_of_schedule round hround schedule,
    accessSafe_of_schedule round hround (schedule_memory1 round schedule),
    accessSafe_of_schedule round hround (schedule_memory2 round schedule),
    accessSafe_of_schedule round hround (schedule_memory3 round schedule),
    accessSafe_of_schedule round hround (schedule_memory4 round schedule),
    accessSafe_of_schedule round hround (schedule_memory5 round schedule),
    accessSafe_of_schedule round hround (schedule_memory6 round schedule),
    accessSafe_of_schedule round hround (schedule_memory7 round schedule)⟩

@[simp] theorem readWord_initialization_storeWord_same (memory : ByteArray)
    (offset : Nat) (value : UInt256) :
    MachineState.readWord (Initialization.storeWord memory offset value) offset =
      value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset value

theorem readWord_initialization_storeWord_disjoint (memory : ByteArray)
    (readStart writeStart : Nat) (value : UInt256)
    (h : Memory.WordDisjoint readStart writeStart) :
    MachineState.readWord
        (Initialization.storeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa [Memory.WordDisjoint, Data.Bytes.natToBytesPadded, ByteArray.size] using h

theorem schedule_constantsMemory (input : ByteArray) :
    ScheduleRows (Initialization.constantsMemory input) := by
  intro round
  unfold MixG.rowWord
  rw [rowOffset_toNat_word]
  have hm : round.toNat % 10 < 10 := Nat.mod_lt _ (by omega)
  interval_cases hr : round.toNat % 10 <;>
    simp only [hr, Initialization.constantsMemory, Initialization.fixedStores,
      Initialization.applyFixedStore, List.foldl_cons, List.foldl_nil,
      Prod.fst, Prod.snd, sigmaPacked] <;>
    norm_num at * <;>
    repeat first
      | rw [readWord_initialization_storeWord_same]
      | rw [readWord_initialization_storeWord_disjoint
          (h := Or.inl (by decide))]

theorem schedule_storeWord {memory : ByteArray} (offset : Nat) (value : UInt256)
    (schedule : ScheduleRows memory) (hoffset : offset + 32 ≤ 1536) :
    ScheduleRows (Initialization.storeWord memory offset value) := by
  intro round
  change MachineState.readWord
      (Memory.storeWord memory offset value) (MixG.rowOffset round).toNat = _
  rw [Memory.readWord_storeWord_disjoint]
  · exact schedule round
  · rw [rowOffset_toNat_word]
    exact Or.inr (by omega)

theorem schedule_t0Memory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.t0Memory input) := by
  apply schedule_storeWord
  · exact schedule_constantsMemory input
  · omega

theorem schedule_t1Memory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.t1Memory input) := by
  apply schedule_storeWord
  · exact schedule_t0Memory input
  · omega

theorem schedule_flaggedMemory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.flaggedMemory input) := by
  apply schedule_storeWord
  · exact schedule_t1Memory input
  · omega

theorem schedule_finalMemory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.finalMemory input) := by
  unfold ScalarInitialization.finalMemory
  split
  · exact schedule_t1Memory input
  · exact schedule_flaggedMemory input

def sigmaIndex (round column : Nat) : Nat :=
  Crypto.Blake2f.SIGMA[round % 10]![column]!

theorem sigmaIndex_lt_16 (round column : Nat) (hcolumn : column < 16) :
    sigmaIndex round column < 16 := by
  have hm : round % 10 < 10 := Nat.mod_lt _ (by omega)
  interval_cases hr : round % 10 <;>
    interval_cases hc : column <;>
    simp only [sigmaIndex] <;>
    simp only [hr] <;>
    decide

theorem messageOffset_sigma_toNat (round column : Nat)
    (hcolumn : column < 16) :
    (MixG.messageOffset (UInt256.ofNat (sigmaPacked (round % 10)))
      (UInt256.ofNat column)).toNat =
      256 + 32 * sigmaIndex round column := by
  have hm : round % 10 < 10 := Nat.mod_lt _ (by omega)
  interval_cases hr : round % 10 <;>
    interval_cases hc : column <;>
    simp only [sigmaIndex] <;>
    simp only [hr] <;>
    norm_num [MixG.messageOffset, sigmaPacked, sigmaIndex,
      Crypto.Blake2f.SIGMA, UInt256.byteAt, UInt256.shiftLeft,
      UInt256.add, Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;>
    decide

/-- The compiled table lookup selects exactly the message lane prescribed by
the pinned `SIGMA` permutation. -/
theorem messageWord_of_represents {memory : ByteArray}
    {message : Array UInt64} (round column : Nat)
    (hround : round < 2 ^ 256) (hcolumn : column < 16)
    (hsize : message.size = 16)
    (schedule : ScheduleRows memory)
    (represents : Memory.RepresentsAt memory 256 message) :
    MixG.messageWord memory
        (MixG.rowWord memory (UInt256.ofNat round)) (UInt256.ofNat column) =
      Word.ofUInt64 message[sigmaIndex round column]! := by
  unfold MixG.messageWord
  rw [schedule (UInt256.ofNat round)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hround]
  rw [messageOffset_sigma_toNat round column hcolumn]
  apply represents
  rw [hsize]
  exact sigmaIndex_lt_16 round column hcolumn

structure MemoryModel (memory : ByteArray) (message vector : Array UInt64) : Prop where
  schedule : ScheduleRows memory
  message : Memory.RepresentsAt memory 256 message
  vector : Memory.RepresentsAt memory 768 vector

/-- One compiled helper call refines one pure `Crypto.Blake2f.mixG` while
preserving both read-only tables. -/
theorem memoryModel_mixG {memory : ByteArray} {message vector : Array UInt64}
    (round ai bi ci di xColumn yColumn : Nat)
    (hround : round < 2 ^ 256)
    (hmessageSize : message.size = 16) (hvectorSize : vector.size = 16)
    (hai : ai < 16) (hbi : bi < 16) (hci : ci < 16) (hdi : di < 16)
    (hxColumn : xColumn < 16) (hyColumn : yColumn < 16)
    (habi : ai ≠ bi) (haci : ai ≠ ci) (hadi : ai ≠ di)
    (hbci : bi ≠ ci) (hbdi : bi ≠ di) (hcdi : ci ≠ di)
    (model : MemoryModel memory message vector) :
    MemoryModel
      (MixG.transition memory
        (UInt256.ofNat (768 + 32 * ai))
        (UInt256.ofNat (768 + 32 * bi))
        (UInt256.ofNat (768 + 32 * ci))
        (UInt256.ofNat (768 + 32 * di))
        (UInt256.ofNat round) (UInt256.ofNat xColumn) (UInt256.ofNat yColumn))
      message
      (Crypto.Blake2f.mixG vector ai bi ci di
        message[sigmaIndex round xColumn]!
        message[sigmaIndex round yColumn]!) := by
  have hai' : ai < vector.size := by omega
  have hbi' : bi < vector.size := by omega
  have hci' : ci < vector.size := by omega
  have hdi' : di < vector.size := by omega
  have htarget (i : Nat) (hi : i < 16) :
      (UInt256.ofNat (768 + 32 * i)).toNat = 768 + 32 * i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  constructor
  · apply schedule_transition
    · exact model.schedule
    all_goals rw [htarget _ (by assumption)]; omega
  · apply MixGCorrectness.representsAt_transition_before
    · exact model.message
    · rw [hmessageSize]
      norm_num
    all_goals rw [hmessageSize, htarget _ (by assumption)]; omega
  · apply MixGCorrectness.representsAt_transition
    · exact model.vector
    · exact messageWord_of_represents round xColumn hround hxColumn
        hmessageSize model.schedule model.message
    · exact messageWord_of_represents round yColumn hround hyColumn
        hmessageSize model.schedule model.message
    · rw [hvectorSize]
      norm_num
    all_goals assumption

def roundVector1 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG vector 0 4 8 12
    message[sigmaIndex round 0]! message[sigmaIndex round 1]!

def roundVector2 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG (roundVector1 message vector round) 1 5 9 13
    message[sigmaIndex round 2]! message[sigmaIndex round 3]!

def roundVector3 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG (roundVector2 message vector round) 2 6 10 14
    message[sigmaIndex round 4]! message[sigmaIndex round 5]!

def roundVector4 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG (roundVector3 message vector round) 3 7 11 15
    message[sigmaIndex round 6]! message[sigmaIndex round 7]!

def roundVector5 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG (roundVector4 message vector round) 0 5 10 15
    message[sigmaIndex round 8]! message[sigmaIndex round 9]!

def roundVector6 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG (roundVector5 message vector round) 1 6 11 12
    message[sigmaIndex round 10]! message[sigmaIndex round 11]!

def roundVector7 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG (roundVector6 message vector round) 2 7 8 13
    message[sigmaIndex round 12]! message[sigmaIndex round 13]!

def roundVector8 (message vector : Array UInt64) (round : Nat) :=
  Crypto.Blake2f.mixG (roundVector7 message vector round) 3 4 9 14
    message[sigmaIndex round 14]! message[sigmaIndex round 15]!

@[simp] theorem roundVector_size (message vector : Array UInt64) (round stage : Nat)
    (hstage : stage ≤ 8) (hvectorSize : vector.size = 16) :
    (match stage with
      | 0 => vector
      | 1 => roundVector1 message vector round
      | 2 => roundVector2 message vector round
      | 3 => roundVector3 message vector round
      | 4 => roundVector4 message vector round
      | 5 => roundVector5 message vector round
      | 6 => roundVector6 message vector round
      | 7 => roundVector7 message vector round
      | _ => roundVector8 message vector round).size = 16 := by
  interval_cases stage <;> simp [roundVector1, roundVector2, roundVector3, roundVector4,
    roundVector5, roundVector6, roundVector7, roundVector8, hvectorSize]

/-- The eight compiled helper calls are exactly one pinned BLAKE2f round. -/
theorem memoryModel_transition {memory : ByteArray}
    {message vector : Array UInt64} (round : Nat)
    (hround : round < 2 ^ 256)
    (hmessageSize : message.size = 16) (hvectorSize : vector.size = 16)
    (model : MemoryModel memory message vector) :
    MemoryModel (Round.transition memory round) message
      (Algorithm.roundStep message vector round) := by
  have model1 : MemoryModel (Round.memory1 memory round) message
      (roundVector1 message vector round) := by
    simpa [Round.memory1, roundVector1,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 0 4 8 12 0 1 hround hmessageSize hvectorSize
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model
  have model2 : MemoryModel (Round.memory2 memory round) message
      (roundVector2 message vector round) := by
    simpa [Round.memory2, roundVector2,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 1 5 9 13 2 3 hround hmessageSize
        (roundVector_size message vector round 1 (by decide) hvectorSize)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model1
  have model3 : MemoryModel (Round.memory3 memory round) message
      (roundVector3 message vector round) := by
    simpa [Round.memory3, roundVector3,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 2 6 10 14 4 5 hround hmessageSize
        (roundVector_size message vector round 2 (by decide) hvectorSize)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model2
  have model4 : MemoryModel (Round.memory4 memory round) message
      (roundVector4 message vector round) := by
    simpa [Round.memory4, roundVector4,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 3 7 11 15 6 7 hround hmessageSize
        (roundVector_size message vector round 3 (by decide) hvectorSize)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model3
  have model5 : MemoryModel (Round.memory5 memory round) message
      (roundVector5 message vector round) := by
    simpa [Round.memory5, roundVector5,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 0 5 10 15 8 9 hround hmessageSize
        (roundVector_size message vector round 4 (by decide) hvectorSize)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model4
  have model6 : MemoryModel (Round.memory6 memory round) message
      (roundVector6 message vector round) := by
    simpa [Round.memory6, roundVector6,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 1 6 11 12 10 11 hround hmessageSize
        (roundVector_size message vector round 5 (by decide) hvectorSize)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model5
  have model7 : MemoryModel (Round.memory7 memory round) message
      (roundVector7 message vector round) := by
    simpa [Round.memory7, roundVector7,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 2 7 8 13 12 13 hround hmessageSize
        (roundVector_size message vector round 6 (by decide) hvectorSize)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model6
  have model8 : MemoryModel (Round.memory8 memory round) message
      (roundVector8 message vector round) := by
    simpa [Round.memory8, roundVector8,
      Challenge.EvmProof.Word.literal_eq_ofNat] using
      memoryModel_mixG round 3 4 9 14 14 15 hround hmessageSize
        (roundVector_size message vector round 7 (by decide) hvectorSize)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) model7
  simpa [Round.transition, Algorithm.roundStep, sigmaIndex,
    roundVector8, roundVector7, roundVector6, roundVector5,
    roundVector4, roundVector3, roundVector2, roundVector1] using model8

/-- Functional invariant for an arbitrary number of compiled rounds. -/
theorem memoryModel_memories {initial : ByteArray}
    {message vector : Array UInt64} (count : Nat)
    (hcount : count < 2 ^ 256)
    (hmessageSize : message.size = 16) (hvectorSize : vector.size = 16)
    (model : MemoryModel initial message vector) :
    MemoryModel (Round.memories initial count) message
      (Algorithm.rounds message count vector) := by
  induction count with
  | zero => simpa [Round.memories, Algorithm.rounds] using model
  | succ count ih =>
      rw [Round.memories, Algorithm.rounds]
      apply memoryModel_transition count (by omega) hmessageSize
      · simpa using hvectorSize
      · exact ih (by omega)

end Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness
