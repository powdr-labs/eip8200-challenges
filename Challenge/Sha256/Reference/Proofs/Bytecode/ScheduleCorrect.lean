import Challenge.Sha256.Reference.Proofs.Bytecode.Schedule
import Mathlib.Data.Nat.Bitwise

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Functional correctness of the reference message schedule

This layer is independent of the schedule's control-flow proof.  It shows
that the memory image produced by the proved bytecode loop contains exactly
the 64 SHA-256 schedule words for the selected padded-message block.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleCorrect

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM

/-- The mathematical SHA-256 message-schedule recurrence for one block. -/
def scheduleWord (padded : ByteArray) (blockOff : Nat) (j : Nat) : UInt32 :=
  if j < 16 then
    Sha256.readBE32 padded (blockOff + j * 4)
  else
    (Sha256.smallSigma1 (scheduleWord padded blockOff (j - 2)) +
      scheduleWord padded blockOff (j - 7)) +
    (Sha256.smallSigma0 (scheduleWord padded blockOff (j - 15)) +
      scheduleWord padded blockOff (j - 16))
termination_by j
decreasing_by all_goals omega

@[simp] theorem scheduleWord_of_lt (padded : ByteArray) (blockOff j : Nat)
    (hj : j < 16) :
    scheduleWord padded blockOff j =
      Sha256.readBE32 padded (blockOff + j * 4) := by
  rw [scheduleWord]
  simp [hj]

theorem scheduleWord_of_ge (padded : ByteArray) (blockOff j : Nat)
    (hj : 16 ≤ j) :
    scheduleWord padded blockOff j =
      (Sha256.smallSigma1 (scheduleWord padded blockOff (j - 2)) +
        scheduleWord padded blockOff (j - 7)) +
      (Sha256.smallSigma0 (scheduleWord padded blockOff (j - 15)) +
        scheduleWord padded blockOff (j - 16)) := by
  rw [scheduleWord]
  simp [show ¬j < 16 by omega]

/-- The recurrence in the exact left-associated spelling used by
`Sha256.compressBlock`. -/
theorem scheduleWord_of_ge_compressBlock (padded : ByteArray)
    (blockOff j : Nat) (hj : 16 ≤ j) :
    scheduleWord padded blockOff j =
      Sha256.smallSigma1 (scheduleWord padded blockOff (j - 2)) +
        scheduleWord padded blockOff (j - 7) +
        Sha256.smallSigma0 (scheduleWord padded blockOff (j - 15)) +
        scheduleWord padded blockOff (j - 16) := by
  rw [scheduleWord_of_ge padded blockOff j hj]
  ac_rfl

theorem scheduleSlot_eq (j : Nat) (hj : j < 64) :
    Schedule.scheduleSlot j = 800 + j * 32 := by
  unfold Schedule.scheduleSlot Accessors.slotOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem scheduleSlot_end_le_messageOffset (j : Nat) (hj : j < 64) :
    Schedule.scheduleSlot j + 32 ≤ Padding.messageOffset := by
  rw [scheduleSlot_eq j hj]
  simp [Padding.messageOffset]
  omega

private theorem mask32_add_distrib (x y : UInt256) :
    Challenge.EvmProof.Word.mask32 (x + y) =
      Challenge.EvmProof.Word.mask32
        (Challenge.EvmProof.Word.mask32 x + Challenge.EvmProof.Word.mask32 y) := by
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.mask32_eq_ofUInt32 x,
    Challenge.EvmProof.Word.mask32_eq_ofUInt32 y,
    Challenge.EvmProof.Word.mask32_add]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [Challenge.EvmProof.Word.toUInt32_toNat, UInt32.toNat_add]
  change ((x.val + y.val).val % 2 ^ 32) =
    (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32
  rw [Fin.val_add]
  change ((x.toNat + y.toNat) % UInt256.size) % 2 ^ 32 = _
  rw [show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.add_mod]

private theorem recurrence_of_words (a b c d : UInt32) :
    Challenge.EvmProof.Word.mask32
        ((Word.evmSmallSigma1 (Challenge.EvmProof.Word.ofUInt32 a) +
            Challenge.EvmProof.Word.ofUInt32 b) +
          (Word.evmSmallSigma0 (Challenge.EvmProof.Word.ofUInt32 c) +
            Challenge.EvmProof.Word.ofUInt32 d)) =
      Challenge.EvmProof.Word.ofUInt32
        ((Sha256.smallSigma1 a + b) + (Sha256.smallSigma0 c + d)) := by
  rw [Word.evmSmallSigma1_ofUInt32, Word.evmSmallSigma0_ofUInt32,
    mask32_add_distrib, Challenge.EvmProof.Word.mask32_add,
    Challenge.EvmProof.Word.mask32_add, Challenge.EvmProof.Word.mask32_add]

/-- The recurrence's `AND` puts the mask first — the backend pushes it last —
while `mask32` is stated value-first. -/
private theorem land_mask32 (y : UInt256) :
    UInt256.land (UInt256.ofNat 4294967295) y =
      Challenge.EvmProof.Word.mask32 y := by
  apply Challenge.EvmProof.Word.word_ext
  show (Fin.land (UInt256.ofNat 4294967295).val y.val).val =
    (Fin.land y.val (UInt256.ofNat 4294967295).val).val
  simp only [Fin.land]
  congr 1
  exact Nat.land_comm _ _

theorem recurrenceWord_eq (s : State) (padded : ByteArray) (blockOff j : Nat)
    (hj16 : 16 ≤ j)
    (h2 : Schedule.wValue s (j - 2) =
      Challenge.EvmProof.Word.ofUInt32 (scheduleWord padded blockOff (j - 2)))
    (h7 : Schedule.wValue s (j - 7) =
      Challenge.EvmProof.Word.ofUInt32 (scheduleWord padded blockOff (j - 7)))
    (h15 : Schedule.wValue s (j - 15) =
      Challenge.EvmProof.Word.ofUInt32 (scheduleWord padded blockOff (j - 15)))
    (h16 : Schedule.wValue s (j - 16) =
      Challenge.EvmProof.Word.ofUInt32 (scheduleWord padded blockOff (j - 16))) :
    Schedule.recurrenceWord s j =
      Challenge.EvmProof.Word.ofUInt32 (scheduleWord padded blockOff j) := by
  rw [scheduleWord_of_ge padded blockOff j hj16]
  -- the inlined sigma blocks *are* the spec's, so the recurrence reduces to it
  simp only [Schedule.recurrenceWord, Functions.smallSigma0Word_eq,
    Functions.smallSigma1Word_eq, land_mask32]
  rw [h2, h7, h15, h16]
  exact recurrence_of_words _ _ _ _

/-- Correctness of all schedule slots below an exclusive upper bound. -/
def SlotsCorrect (s : State) (padded : ByteArray) (blockOff upto : Nat) : Prop :=
  ∀ k, k < upto → Schedule.wValue s k =
    Challenge.EvmProof.Word.ofUInt32 (scheduleWord padded blockOff k)

/-- Exact initial-memory seam required by the schedule proof: the sixteen
four-byte words addressed through `msgOff` are the selected padded block. -/
def PaddedBlockAt (memory : ByteArray) (msgOff : UInt256)
    (padded : ByteArray) (blockOff : Nat) : Prop :=
  ∀ k, k < 16 → Schedule.initialWord memory msgOff k =
    Challenge.EvmProof.Word.ofUInt32
      (Sha256.readBE32 padded (blockOff + k * 4))

@[simp] theorem afterFirstIteration_memory (s : State)
    (msgOff : UInt256) (rest : List UInt256) (j : Nat) :
    (Schedule.afterFirstIteration s msgOff returnDest rest j).memory =
      MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded
          (Schedule.initialWord s.memory msgOff j).toNat 32)
        (Schedule.scheduleSlot j) := by
  rfl

@[simp] theorem afterSecondIteration_memory (s : State)
    (msgOff : UInt256) (rest : List UInt256) (j : Nat) :
    (Schedule.afterSecondIteration s msgOff returnDest rest j).memory =
      MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded
          (Schedule.recurrenceWord s msgOff returnDest rest j).toNat 32)
        (Schedule.scheduleSlot j) := by
  rfl

private theorem initialWord_write_schedule (memory : ByteArray)
    (msgOff : UInt256) (readIndex writeIndex : Nat)
    (hwrite : writeIndex < 64)
    (hseparated : Padding.messageOffset ≤
      Schedule.loadOffset msgOff readIndex) :
    Schedule.initialWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded
            (Schedule.initialWord memory msgOff writeIndex).toNat 32)
          (Schedule.scheduleSlot writeIndex))
        msgOff readIndex =
      Schedule.initialWord memory msgOff readIndex := by
  unfold Schedule.initialWord
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  exact Or.inr (by
    have h := le_trans (scheduleSlot_end_le_messageOffset writeIndex hwrite)
      hseparated
    simpa [Data.Bytes.natToBytesPadded, ByteArray.size] using h)

theorem firstLoopState_initialWord (s : State) (msgOff : UInt256)
    (rest : List UInt256) (n k : Nat) (hn : n ≤ 16)
    (hseparated : Padding.messageOffset ≤ Schedule.loadOffset msgOff k) :
    Schedule.initialWord
        (Schedule.firstLoopState s msgOff rest n).memory msgOff k =
      Schedule.initialWord s.memory msgOff k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.firstLoopState, afterFirstIteration_memory]
      rw [initialWord_write_schedule _ _ k n (by omega) hseparated]
      exact ih (by omega)

theorem firstLoopState_slots (s : State) (msgOff : UInt256)
    (rest : List UInt256) (padded : ByteArray) (blockOff n : Nat)
    (hn : n ≤ 16)
    (hseparated : ∀ k, k < 16 →
      Padding.messageOffset ≤ Schedule.loadOffset msgOff k)
    (hread : ∀ k, k < 16 →
      Schedule.initialWord s.memory msgOff k =
        Challenge.EvmProof.Word.ofUInt32
          (Sha256.readBE32 padded (blockOff + k * 4))) :
    SlotsCorrect (Schedule.firstLoopState s msgOff rest n)
      padded blockOff n := by
  induction n with
  | zero =>
      intro k hk
      omega
  | succ n ih =>
      intro k hk
      rw [Schedule.firstLoopState]
      simp only [Schedule.wValue, afterFirstIteration_memory]
      by_cases hkn : k = n
      · subst k
        rw [Challenge.EvmProof.Memory.readWord_writeWord]
        rw [firstLoopState_initialWord s msgOff returnDest rest n n
          (by omega) (hseparated n (by omega))]
        rw [scheduleWord_of_lt padded blockOff n (by omega)]
        exact hread n (by omega)
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega) k (by omega)
        · left
          rw [scheduleSlot_eq k (by omega), scheduleSlot_eq n (by omega)]
          omega

theorem secondLoopState_slots (s : State) (msgOff : UInt256)
    (rest : List UInt256) (padded : ByteArray) (blockOff n : Nat)
    (hn : n ≤ 48) (hbase : SlotsCorrect s padded blockOff 16) :
    SlotsCorrect (Schedule.secondLoopState s msgOff rest n)
      padded blockOff (16 + n) := by
  induction n with
  | zero =>
      intro k hk
      change Schedule.wValue s k = _
      exact hbase k (by simpa using hk)
  | succ n ih =>
      intro k hk
      rw [Schedule.secondLoopState]
      simp only [Schedule.wValue, afterSecondIteration_memory]
      let j := 16 + n
      by_cases hkj : k = j
      · subst k
        rw [Challenge.EvmProof.Memory.readWord_writeWord]
        apply recurrenceWord_eq (hj16 := by omega)
        · exact ih (by omega) (j - 2) (by omega)
        · exact ih (by omega) (j - 7) (by omega)
        · exact ih (by omega) (j - 15) (by omega)
        · exact ih (by omega) (j - 16) (by omega)
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega) k (by omega)
        · left
          rw [scheduleSlot_eq k (by omega), scheduleSlot_eq j (by omega)]
          omega

/-- Generic end-to-end functional postcondition for the complete proved
schedule state.  The two hypotheses are precisely the memory-reader seam a
caller must establish for its chosen message layout. -/
theorem scheduleResult_slots (s : State) (msgOff : UInt256)
    (rest : List UInt256) (padded : ByteArray) (blockOff : Nat)
    (hseparated : ∀ k, k < 16 →
      Padding.messageOffset ≤ Schedule.loadOffset msgOff k)
    (hread : ∀ k, k < 16 →
      Schedule.initialWord s.memory msgOff k =
        Challenge.EvmProof.Word.ofUInt32
          (Sha256.readBE32 padded (blockOff + k * 4))) :
    SlotsCorrect (Schedule.scheduleResult s rest)
      padded blockOff 64 := by
  let q := Schedule.firstLoopState s msgOff rest 16
  have hfirst : SlotsCorrect q padded blockOff 16 :=
    firstLoopState_slots s msgOff rest padded blockOff 16
      (by omega) hseparated hread
  have hsecond := secondLoopState_slots q rest
    padded blockOff 48 (by omega) hfirst
  intro k hk
  change Schedule.wValue
      (Schedule.secondLoopState q rest 48) k = _
  exact hsecond k (by simpa using hk)

/-- Caller-facing form using the concrete initial-memory predicate. -/
theorem scheduleResult_slots_of_paddedBlockAt (s : State)
    (msgOff : UInt256) (rest : List UInt256)
    (padded : ByteArray) (blockOff : Nat)
    (hseparated : ∀ k, k < 16 →
      Padding.messageOffset ≤ Schedule.loadOffset msgOff k)
    (hblock : PaddedBlockAt s.memory msgOff padded blockOff) :
    SlotsCorrect (Schedule.scheduleResult s rest)
      padded blockOff 64 := by
  apply scheduleResult_slots
  · exact hseparated
  · exact hblock

end Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleCorrect
