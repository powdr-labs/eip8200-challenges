import Challenge.Sha256.Submissions.Sha256Fast.Proofs.Body
import Challenge.Sha256.Reference.Proofs.Bytecode.PaddedBlockBridge

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-! Functional invariant for Sha256Fast's doubled-word message schedule. -/

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.ScheduleCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Word
open Challenge.Sha256.Fast

abbrev scheduleWord :=
  Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleCorrect.scheduleWord

def wOffset (i : Nat) : Nat := 384 + i * 32

def wValue (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (wOffset i)

def writeW (memory : ByteArray) (i : Nat) (value : UInt32) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded (dbl (ofUInt32 value)).toNat 32)
    (wOffset i)

@[simp] theorem wValue_writeW_same (memory : ByteArray) (i : Nat)
    (value : UInt32) :
    wValue (writeW memory i value) i = dbl (ofUInt32 value) := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory (wOffset i)
    (dbl (ofUInt32 value))

theorem wValue_writeW_ne (memory : ByteArray) (read write : Nat)
    (value : UInt32) (hne : read ≠ write) :
    wValue (writeW memory write value) read = wValue memory read := by
  unfold wValue writeW
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  simp only [wOffset]
  rcases lt_or_gt_of_ne hne with h | h
  · left; omega
  · right; omega

def WCorrect (memory padded : ByteArray) (blockOff upto : Nat) : Prop :=
  ∀ i, i < upto →
    wValue memory i = dbl (ofUInt32 (scheduleWord padded blockOff i))

theorem WCorrect.zero (memory padded : ByteArray) (blockOff : Nat) :
    WCorrect memory padded blockOff 0 := by
  intro i hi
  omega

theorem WCorrect.writeNext {memory padded : ByteArray} {blockOff upto : Nat}
    (h : WCorrect memory padded blockOff upto) :
    WCorrect (writeW memory upto (scheduleWord padded blockOff upto))
      padded blockOff (upto + 1) := by
  intro i hi
  by_cases heq : i = upto
  · subst i
    exact wValue_writeW_same _ _ _
  · rw [wValue_writeW_ne _ _ _ _ heq]
    exact h i (by omega)

def writeSchedule (memory padded : ByteArray) (blockOff : Nat) : Nat → ByteArray
  | 0 => memory
  | n + 1 => writeW (writeSchedule memory padded blockOff n) n
      (scheduleWord padded blockOff n)

theorem writeSchedule_correct (memory padded : ByteArray) (blockOff n : Nat) :
    WCorrect (writeSchedule memory padded blockOff n) padded blockOff n := by
  induction n with
  | zero => exact WCorrect.zero _ _ _
  | succ n ih => exact ih.writeNext

def writeFrom (memory padded : ByteArray) (blockOff start : Nat) :
    Nat → ByteArray
  | 0 => memory
  | n + 1 => writeW (writeFrom memory padded blockOff start n) (start + n)
      (scheduleWord padded blockOff (start + n))

theorem writeFrom_correct {memory padded : ByteArray} {blockOff start : Nat}
    (h : WCorrect memory padded blockOff start) :
    ∀ n, WCorrect (writeFrom memory padded blockOff start n)
      padded blockOff (start + n) := by
  intro n
  induction n with
  | zero =>
      change WCorrect memory padded blockOff start
      exact h
  | succ n ih =>
      simpa [writeFrom, Nat.add_assoc] using ih.writeNext

theorem writeSchedule_add_eight (memory padded : ByteArray)
    (blockOff n : Nat) :
    writeFrom (writeSchedule memory padded blockOff n) padded blockOff n 8 =
      writeSchedule memory padded blockOff (n + 8) := by
  rfl

def initialMemory (memory : ByteArray) : ByteArray :=
  writeSchedule memory memory 288 16

theorem initialMemory_correct (memory : ByteArray) :
    WCorrect (initialMemory memory) memory 288 16 := by
  exact writeSchedule_correct memory memory 288 16

/-- The generated straight-line prefix establishes the first sixteen schedule
words.  The specification is deliberately phrased over the pre-prefix memory,
whose 64 bytes at `SCR = 288` are the staged compression block. -/
theorem run_initialSchedule (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 4)
    (hstack : s.stack = returnDest :: rest) :
    Challenge.EvmProof.Stepper.runLocatedBlock Loop.Body.initialSchedulePath s =
      some { s with
        pc := UInt256.ofNat 295
        activeWords := UInt256.ofNat 140
        memory := initialMemory s.memory
        stack := UInt256.ofNat 0 :: returnDest :: rest } := by
  have h := Loop.Body.run_initialSchedule s returnDest rest hcap haw hrun hpc hstack
  simpa [initialMemory, writeSchedule, writeW, wOffset,
    Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleCorrect.scheduleWord_of_lt,
    Challenge.Sha256.Reference.Proofs.Bytecode.PaddedBlockBridge.shiftRight_readWord_224]
    using h

private theorem groupAddress (g base : Nat) (hg : g < 6)
    (hbase : base ≤ 1120) :
    (UInt256.ofNat base + UInt256.ofNat (256 * g)).toNat = base + 256 * g := by
  rw [word_toNat_add, word_toNat_ofNat, word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- One generated eight-word group extends the mathematical schedule by eight
slots.  Keeping this theorem group-parametric avoids six copies of the large
symbolic evaluator result. -/
theorem run_scheduleGroup (s : State) (padded : ByteArray) (blockOff g : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hg : g < 6) (hcap : rest.length < 999)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 295)
    (hstack : s.stack = UInt256.ofNat (256 * g) :: returnDest :: rest)
    (hW : WCorrect s.memory padded blockOff (16 + 8 * g)) :
    Challenge.EvmProof.Stepper.runLocatedBlock Loop.psched_compute s =
      some { s with
        pc := UInt256.ofNat 883
        activeWords := UInt256.ofNat 140
        memory := writeFrom s.memory padded blockOff (16 + 8 * g) 8
        stack := [UInt256.ofNat 294,
          UInt256.lt
            (UInt256.ofNat 256 + UInt256.ofNat (256 * g))
            (UInt256.ofNat 1536),
          UInt256.ofNat 256 + UInt256.ofNat (256 * g), returnDest] ++ rest } := by
  let W := fun i => scheduleWord padded blockOff i
  have readAt : ∀ base index, base ≤ 1120 →
      base + 256 * g = wOffset index → index < 16 + 8 * g →
      MachineState.readWord s.memory
          (UInt256.ofNat base + UInt256.ofNat (256 * g)).toNat =
        dbl (ofUInt32 (W index)) := by
    intro base index hb haddr hi
    rw [groupAddress g base hg hb]
    rw [haddr]
    exact hW index hi
  have h := Loop.sched_iter_compute s
    (W (14 + 8 * g)) (W (9 + 8 * g))
    (W (1 + 8 * g)) (W (0 + 8 * g))
    (W (15 + 8 * g)) (W (10 + 8 * g))
    (W (2 + 8 * g)) (W (11 + 8 * g))
    (W (3 + 8 * g)) (W (12 + 8 * g))
    (W (4 + 8 * g)) (W (13 + 8 * g))
    (W (5 + 8 * g)) (W (6 + 8 * g))
    (W (7 + 8 * g)) (W (8 + 8 * g))
    (UInt256.ofNat (256 * g)) (returnDest :: rest) (by simp; omega)
    (by rw [word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    haw hrun hpc hstack
    (readAt 832 (14 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 672 (9 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 416 (1 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 384 (0 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 864 (15 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 704 (10 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 448 (2 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 736 (11 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 480 (3 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 768 (12 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 512 (4 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 800 (13 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 544 (5 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 576 (6 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 608 (7 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
    (readAt 640 (8 + 8 * g) (by omega) (by simp [wOffset]; omega) (by omega))
  have recurrence (j : Nat) (hj : 16 ≤ j) :
      Sha256.smallSigma1 (W (j - 2)) + W (j - 7) +
          Sha256.smallSigma0 (W (j - 15)) + W (j - 16) = W j := by
    exact (Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleCorrect.scheduleWord_of_ge_compressBlock
      padded blockOff j hj).symm
  have hs0 : Sha256.smallSigma1 (W (14 + 8 * g)) + W (9 + 8 * g) +
      Sha256.smallSigma0 (W (1 + 8 * g)) + W (0 + 8 * g) =
        W (16 + 8 * g) := by
    simpa only [show 16 + 8 * g - 2 = 14 + 8 * g by omega,
      show 16 + 8 * g - 7 = 9 + 8 * g by omega,
      show 16 + 8 * g - 15 = 1 + 8 * g by omega,
      show 16 + 8 * g - 16 = 0 + 8 * g by omega] using
        recurrence (16 + 8 * g) (by omega)
  have hs1 : Sha256.smallSigma1 (W (15 + 8 * g)) + W (10 + 8 * g) +
      Sha256.smallSigma0 (W (2 + 8 * g)) + W (1 + 8 * g) =
        W (17 + 8 * g) := by
    simpa only [show 17 + 8 * g - 2 = 15 + 8 * g by omega,
      show 17 + 8 * g - 7 = 10 + 8 * g by omega,
      show 17 + 8 * g - 15 = 2 + 8 * g by omega,
      show 17 + 8 * g - 16 = 1 + 8 * g by omega] using
        recurrence (17 + 8 * g) (by omega)
  have hs2 : Sha256.smallSigma1 (W (16 + 8 * g)) + W (11 + 8 * g) +
      Sha256.smallSigma0 (W (3 + 8 * g)) + W (2 + 8 * g) =
        W (18 + 8 * g) := by
    simpa only [show 18 + 8 * g - 2 = 16 + 8 * g by omega,
      show 18 + 8 * g - 7 = 11 + 8 * g by omega,
      show 18 + 8 * g - 15 = 3 + 8 * g by omega,
      show 18 + 8 * g - 16 = 2 + 8 * g by omega] using
        recurrence (18 + 8 * g) (by omega)
  have hs3 : Sha256.smallSigma1 (W (17 + 8 * g)) + W (12 + 8 * g) +
      Sha256.smallSigma0 (W (4 + 8 * g)) + W (3 + 8 * g) =
        W (19 + 8 * g) := by
    simpa only [show 19 + 8 * g - 2 = 17 + 8 * g by omega,
      show 19 + 8 * g - 7 = 12 + 8 * g by omega,
      show 19 + 8 * g - 15 = 4 + 8 * g by omega,
      show 19 + 8 * g - 16 = 3 + 8 * g by omega] using
        recurrence (19 + 8 * g) (by omega)
  have hs4 : Sha256.smallSigma1 (W (18 + 8 * g)) + W (13 + 8 * g) +
      Sha256.smallSigma0 (W (5 + 8 * g)) + W (4 + 8 * g) =
        W (20 + 8 * g) := by
    simpa only [show 20 + 8 * g - 2 = 18 + 8 * g by omega,
      show 20 + 8 * g - 7 = 13 + 8 * g by omega,
      show 20 + 8 * g - 15 = 5 + 8 * g by omega,
      show 20 + 8 * g - 16 = 4 + 8 * g by omega] using
        recurrence (20 + 8 * g) (by omega)
  have hs5 : Sha256.smallSigma1 (W (19 + 8 * g)) + W (14 + 8 * g) +
      Sha256.smallSigma0 (W (6 + 8 * g)) + W (5 + 8 * g) =
        W (21 + 8 * g) := by
    simpa only [show 21 + 8 * g - 2 = 19 + 8 * g by omega,
      show 21 + 8 * g - 7 = 14 + 8 * g by omega,
      show 21 + 8 * g - 15 = 6 + 8 * g by omega,
      show 21 + 8 * g - 16 = 5 + 8 * g by omega] using
        recurrence (21 + 8 * g) (by omega)
  have hs6 : Sha256.smallSigma1 (W (20 + 8 * g)) + W (15 + 8 * g) +
      Sha256.smallSigma0 (W (7 + 8 * g)) + W (6 + 8 * g) =
        W (22 + 8 * g) := by
    simpa only [show 22 + 8 * g - 2 = 20 + 8 * g by omega,
      show 22 + 8 * g - 7 = 15 + 8 * g by omega,
      show 22 + 8 * g - 15 = 7 + 8 * g by omega,
      show 22 + 8 * g - 16 = 6 + 8 * g by omega] using
        recurrence (22 + 8 * g) (by omega)
  have hs7 : Sha256.smallSigma1 (W (21 + 8 * g)) + W (16 + 8 * g) +
      Sha256.smallSigma0 (W (8 + 8 * g)) + W (7 + 8 * g) =
        W (23 + 8 * g) := by
    simpa only [show 23 + 8 * g - 2 = 21 + 8 * g by omega,
      show 23 + 8 * g - 7 = 16 + 8 * g by omega,
      show 23 + 8 * g - 15 = 8 + 8 * g by omega,
      show 23 + 8 * g - 16 = 7 + 8 * g by omega] using
        recurrence (23 + 8 * g) (by omega)
  simp_rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h
  have hi1 : 16 + 8 * g + 1 = 17 + 8 * g := by omega
  have hi2 : 16 + 8 * g + 2 = 18 + 8 * g := by omega
  have hi3 : 16 + 8 * g + 3 = 19 + 8 * g := by omega
  have hi4 : 16 + 8 * g + 4 = 20 + 8 * g := by omega
  have hi5 : 16 + 8 * g + 5 = 21 + 8 * g := by omega
  have hi6 : 16 + 8 * g + 6 = 22 + 8 * g := by omega
  have hi7 : 16 + 8 * g + 7 = 23 + 8 * g := by omega
  have ha0 : 384 + (16 + 8 * g) * 32 = 896 + 256 * g := by omega
  have ha1 : 384 + (17 + 8 * g) * 32 = 928 + 256 * g := by omega
  have ha2 : 384 + (18 + 8 * g) * 32 = 960 + 256 * g := by omega
  have ha3 : 384 + (19 + 8 * g) * 32 = 992 + 256 * g := by omega
  have ha4 : 384 + (20 + 8 * g) * 32 = 1024 + 256 * g := by omega
  have ha5 : 384 + (21 + 8 * g) * 32 = 1056 + 256 * g := by omega
  have ha6 : 384 + (22 + 8 * g) * 32 = 1088 + 256 * g := by omega
  have ha7 : 384 + (23 + 8 * g) * 32 = 1120 + 256 * g := by omega
  rw [groupAddress g 896 hg (by omega), groupAddress g 928 hg (by omega),
    groupAddress g 960 hg (by omega), groupAddress g 992 hg (by omega),
    groupAddress g 1024 hg (by omega), groupAddress g 1056 hg (by omega),
    groupAddress g 1088 hg (by omega), groupAddress g 1120 hg (by omega)] at h
  simpa [W, writeFrom, writeW, wOffset, hi1, hi2, hi3, hi4, hi5,
    hi6, hi7, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7] using h

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.ScheduleCorrect
