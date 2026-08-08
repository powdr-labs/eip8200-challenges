import Challenge.Blake2f.Reference.Proofs.Bytecode.RoundGas
import Challenge.Blake2f.Reference.Proofs.Bytecode.StoreLE64

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! Direct control-flow model for the post-round fold and output loop. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.Output

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def outputWord (memory : ByteArray) (i : Nat) : UInt256 :=
  UInt256.xor
    (UInt256.xor
      (MachineState.readWord memory (32 * i))
      (MachineState.readWord memory (768 + 32 * i)))
    (MachineState.readWord memory (1024 + 32 * i))

def outputMemory (memory : ByteArray) : Nat → ByteArray
  | 0 => memory
  | i + 1 =>
      StoreLE64.writtenMemory (outputMemory memory i) (1280 + 8 * i)
        (outputWord (outputMemory memory i) i) 8

def baseState (s : State) (memory : ByteArray) : State :=
  { s with memory, activeWords := UInt256.ofNat 58 }

def loopState (s : State) (initial : ByteArray) (rounds flag : UInt256)
    (i : Nat) : State :=
  { baseState s (outputMemory initial i) with
    pc := UInt256.ofNat 1098
    stack := [UInt256.ofNat i, rounds, flag] }

def returnedState (s : State) (initial : ByteArray) (rounds flag : UInt256)
    (i : Nat) : State :=
  StoreLE64.finalState (baseState s (outputMemory initial i))
    (UInt256.ofNat (1280 + 8 * i))
    (outputWord (outputMemory initial i) i) (UInt256.ofNat 1149)
    [outputWord (outputMemory initial i) i, UInt256.ofNat i, rounds, flag]

def finalState (s : State) (initial : ByteArray) (rounds flag : UInt256) : State :=
  { baseState s (outputMemory initial 8) with
    pc := UInt256.ofNat 1168
    stack := [rounds, flag]
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory initial 8) 1280 64 }

def roundExitPath := Artifact.locatedPath [436, 437, 438, 439, 440, 441]
def initPath := Artifact.locatedPath [537, 538, 539]
def testPath := Artifact.locatedPath [540, 541, 542, 543, 544, 545, 546]
def setupPath := Artifact.locatedPath
  [547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558,
    559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570,
    571, 572, 573]
def incrementPath := Artifact.locatedPath
  [574, 575, 576, 577, 578, 579, 580, 581, 582]
def finishPath := Artifact.locatedPath [583, 584, 585, 586, 587]

private theorem ofNatAdd (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

private theorem activeWordsAfter_eq (offset size : Nat)
    (hend : offset + size ≤ 58 * 32) :
    MachineState.activeWordsAfter 58 offset size = 58 := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hdiv : (offset + size - 1) / 32 < 58 := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 32)).2
      omega
    exact Nat.succ_le_of_lt hdiv

private theorem valid51 : Decode.isValidJumpDest referenceBytecode 51 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 40 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem valid1098 : Decode.isValidJumpDest referenceBytecode 1098 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 540 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem valid1095 : Decode.isValidJumpDest referenceBytecode 1095 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 537 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem valid1161 : Decode.isValidJumpDest referenceBytecode 1161 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 583 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

theorem run_roundExit (s : State) (memory : ByteArray) (rounds flag : UInt256)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock roundExitPath
        (Round.loopState s rounds.toNat rounds flag memory) =
      some { Round.loopState s rounds.toNat rounds flag memory with
        pc := UInt256.ofNat 1095 } := by
  have hroundWord : UInt256.ofNat rounds.toNat = rounds := ofNat_toNat rounds
  simp (config := { maxSteps := 300000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      roundExitPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Round.loopState, Round.baseState, hroundWord, hrun, hcode,
      valid1095,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue, ofNatAdd]

theorem run_init (s : State) (memory : ByteArray) (rounds flag : UInt256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock initPath
        { Round.loopState s rounds.toNat rounds flag memory with
          pc := UInt256.ofNat 1095 } =
      some (loopState s memory rounds flag 0) := by
  have hroundWord : UInt256.ofNat rounds.toNat = rounds := ofNat_toNat rounds
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      initPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Round.loopState, Round.baseState, loopState, baseState, outputMemory,
      hroundWord, hzero, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat, ofNatAdd]

theorem run_test_continue (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (i : Nat) (hi : i < 8)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock testPath
        (loopState s initial rounds flag i) =
      some { loopState s initial rounds flag i with pc := UInt256.ofNat 1108 } := by
  have hito : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp (config := { maxSteps := 250000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      testPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, baseState, hi, hito, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue, ofNatAdd]

theorem run_test_exit (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock testPath
        (loopState s initial rounds flag 8) =
      some { loopState s initial rounds flag 8 with pc := UInt256.ofNat 1161 } := by
  simp (config := { maxSteps := 250000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      testPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, baseState, hrun, hcode, valid1161,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue, ofNatAdd]

theorem run_setup (s : State) (initial : ByteArray) (rounds flag : UInt256)
    (i : Nat) (hi : i < 8) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPath
        { loopState s initial rounds flag i with pc := UInt256.ofNat 1108 } =
      some { baseState s (outputMemory initial i) with
        pc := UInt256.ofNat 51
        stack := [UInt256.ofNat (1280 + 8 * i),
          outputWord (outputMemory initial i) i, UInt256.ofNat 1149,
          outputWord (outputMemory initial i) i, UInt256.ofNat i, rounds, flag] } := by
  have hshift5 : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * i) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by omega)]
    congr 1
    omega
  have hshift3 : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 3) =
      UInt256.ofNat (8 * i) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by omega)]
    congr 1
    omega
  have hsource0 : 32 * i + 32 ≤ 58 * 32 := by omega
  have hsource1 : 768 + 32 * i + 32 ≤ 58 * 32 := by omega
  have hsource2 : 1024 + 32 * i + 32 ≤ 58 * 32 := by omega
  have hactive0 := activeWordsAfter_eq (32 * i) 32 hsource0
  have hactive1 := activeWordsAfter_eq (768 + 32 * i) 32 hsource1
  have hactive2 := activeWordsAfter_eq (1024 + 32 * i) 32 hsource2
  have hmod0 : 32 * i % 2 ^ 256 = 32 * i := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (768 + 32 * i) % 2 ^ 256 = 768 + 32 * i :=
    Nat.mod_eq_of_lt (by omega)
  have hmod2 : (1024 + 32 * i) % 2 ^ 256 = 1024 + 32 * i :=
    Nat.mod_eq_of_lt (by omega)
  norm_num at hmod0 hmod1 hmod2
  have hcap3 : 3 < 1024 := by omega
  have hcap4 : 4 < 1024 := by omega
  have hcap5 : 5 < 1024 := by omega
  have hcap6 : 6 < 1024 := by omega
  have hcap7 : 7 < 1024 := by omega
  have hcap8 : 8 < 1024 := by omega
  simp (config := { maxSteps := 2000000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setupPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, baseState, outputWord, hi, hshift5, hshift3, hrun, hcode,
      valid51, UInt256.xor, ofNatAdd, hactive0, hactive1, hactive2,
      activeWordsAfter_eq, State.activeWordsAfterUInt256,
      hcap3, hcap4, hcap5, hcap6, hcap7, hcap8,
      Nat.mod_eq_of_lt hmod0, Nat.mod_eq_of_lt hmod1, Nat.mod_eq_of_lt hmod2,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_increment (s : State) (initial : ByteArray)
    (rounds flag : UInt256) (i : Nat) (hi : i < 8)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath
        (returnedState s initial rounds flag i) =
      some (loopState s initial rounds flag (i + 1)) := by
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have haddress : 1280 + 8 * i < 2 ^ 256 := by omega
  have hmod : (1280 + 8 * i) % 2 ^ 256 = 1280 + 8 * i :=
    Nat.mod_eq_of_lt haddress
  norm_num at hmod
  have hcap3 : 3 < 1024 := by omega
  have hcap4 : 4 < 1024 := by omega
  have hcap5 : 5 < 1024 := by omega
  have hswap (a b : UInt256) (rho : List UInt256) :
      (a :: b :: rho).exchange 0 1 = some (b :: a :: rho) := by
    rfl
  simp (config := { maxSteps := 600000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      incrementPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      returnedState, StoreLE64.finalState, loopState, baseState,
      outputMemory, hi, hadd, haddress, Nat.mod_eq_of_lt hmod,
      hrun, hcode, valid1098, ofNatAdd, hswap,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_finish (s : State) (initial : ByteArray) (rounds flag : UInt256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishPath
        { loopState s initial rounds flag 8 with pc := UInt256.ofNat 1161 } =
      some (finalState s initial rounds flag) := by
  have hpc1165 : UInt256.ofNat 1163 + UInt256.ofNat 2 = UInt256.ofNat 1165 :=
    ofNatAdd 1163 2 (by omega)
  have hpc1168 : UInt256.ofNat 1165 + UInt256.ofNat 3 = UInt256.ofNat 1168 :=
    ofNatAdd 1165 3 (by omega)
  have hactive : MachineState.activeWordsAfter 58 1280 64 = 58 := by decide
  simp (config := { maxSteps := 250000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      finishPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, finalState, baseState, hrun, hpc1165, hpc1168, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

end Challenge.Blake2f.Reference.Proofs.Bytecode.Output
