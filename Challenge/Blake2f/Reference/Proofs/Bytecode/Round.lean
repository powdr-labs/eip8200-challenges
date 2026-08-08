import Challenge.Blake2f.Reference.Proofs.Bytecode.MixGCorrectness
import Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitializationGas

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! Direct control-flow model for one compiled BLAKE2f round. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.Round

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def baseState (s : State) (memory : ByteArray) : State :=
  { s with memory, activeWords := UInt256.ofNat 58 }

def loopState (s : State) (round : Nat) (rounds flag : UInt256)
    (memory : ByteArray) : State :=
  { baseState s memory with
    pc := UInt256.ofNat 878
    stack := [UInt256.ofNat round, rounds, flag] }

def tail (round : Nat) (rounds flag : UInt256) : List UInt256 :=
  [UInt256.ofNat round, rounds, flag]

def memory1 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition memory 768 896 1024 1152 (UInt256.ofNat round) 0 1

def memory2 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition (memory1 memory round) 800 928 1056 1184
    (UInt256.ofNat round) 2 3

def memory3 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition (memory2 memory round) 832 960 1088 1216
    (UInt256.ofNat round) 4 5

def memory4 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition (memory3 memory round) 864 992 1120 1248
    (UInt256.ofNat round) 6 7

def memory5 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition (memory4 memory round) 768 928 1088 1248
    (UInt256.ofNat round) 8 9

def memory6 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition (memory5 memory round) 800 960 1120 1152
    (UInt256.ofNat round) 10 11

def memory7 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition (memory6 memory round) 832 992 1024 1184
    (UInt256.ofNat round) 12 13

def memory8 (memory : ByteArray) (round : Nat) : ByteArray :=
  MixG.transition (memory7 memory round) 864 896 1056 1216
    (UInt256.ofNat round) 14 15

def transition := memory8

def testSetupPath := Artifact.locatedPath
  [436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447,
    448, 449, 450, 451]
def setup2Path := Artifact.locatedPath
  [452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462]
def setup3Path := Artifact.locatedPath
  [463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473]
def setup4Path := Artifact.locatedPath
  [474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484]
def setup5Path := Artifact.locatedPath
  [485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]
def setup6Path := Artifact.locatedPath
  [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506]
def setup7Path := Artifact.locatedPath
  [507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517]
def setup8Path := Artifact.locatedPath
  [518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528]
def incrementPath := Artifact.locatedPath
  [529, 530, 531, 532, 533, 534, 535, 536, 435]

private theorem jumpDest96 : Decode.isValidJumpDest referenceBytecode 96 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 75 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem jumpDest877 : Decode.isValidJumpDest referenceBytecode 877 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 435 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem ofNatAdd (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

theorem run_testSetup (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hround : round < rounds.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock testSetupPath
        (loopState s round rounds flag memory) =
      some (MixG.entryState (baseState s memory)
        768 896 1024 1152 (UInt256.ofNat round) 0 1 909
        (tail round rounds flag)) := by
  have hroundNat : (UInt256.ofNat round).toNat = round := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans hround rounds.val.isLt
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      testSetupPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, baseState, tail, MixG.entryState,
      hrun, hcode, hround, hroundNat, hzero,
      jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_setup2 (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup2Path
        (MixG.finalState (baseState s memory)
          768 896 1024 1152 (UInt256.ofNat round) 0 1 909
          (tail round rounds flag)) =
      some (MixG.entryState (baseState s (memory1 memory round))
        800 928 1056 1184 (UInt256.ofNat round) 2 3 934
        (tail round rounds flag)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setup2Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, MixG.entryState, memory1, baseState, tail,
      hrun, hcode, jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_setup3 (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup3Path
        (MixG.finalState (baseState s (memory1 memory round))
          800 928 1056 1184 (UInt256.ofNat round) 2 3 934
          (tail round rounds flag)) =
      some (MixG.entryState (baseState s (memory2 memory round))
        832 960 1088 1216 (UInt256.ofNat round) 4 5 959
        (tail round rounds flag)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setup3Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, MixG.entryState, memory1, memory2, baseState, tail,
      hrun, hcode, jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_setup4 (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup4Path
        (MixG.finalState (baseState s (memory2 memory round))
          832 960 1088 1216 (UInt256.ofNat round) 4 5 959
          (tail round rounds flag)) =
      some (MixG.entryState (baseState s (memory3 memory round))
        864 992 1120 1248 (UInt256.ofNat round) 6 7 984
        (tail round rounds flag)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setup4Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, MixG.entryState, memory2, memory3, baseState, tail,
      hrun, hcode, jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_setup5 (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup5Path
        (MixG.finalState (baseState s (memory3 memory round))
          864 992 1120 1248 (UInt256.ofNat round) 6 7 984
          (tail round rounds flag)) =
      some (MixG.entryState (baseState s (memory4 memory round))
        768 928 1088 1248 (UInt256.ofNat round) 8 9 1009
        (tail round rounds flag)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setup5Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, MixG.entryState, memory3, memory4, baseState, tail,
      hrun, hcode, jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_setup6 (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup6Path
        (MixG.finalState (baseState s (memory4 memory round))
          768 928 1088 1248 (UInt256.ofNat round) 8 9 1009
          (tail round rounds flag)) =
      some (MixG.entryState (baseState s (memory5 memory round))
        800 960 1120 1152 (UInt256.ofNat round) 10 11 1034
        (tail round rounds flag)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setup6Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, MixG.entryState, memory4, memory5, baseState, tail,
      hrun, hcode, jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_setup7 (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup7Path
        (MixG.finalState (baseState s (memory5 memory round))
          800 960 1120 1152 (UInt256.ofNat round) 10 11 1034
          (tail round rounds flag)) =
      some (MixG.entryState (baseState s (memory6 memory round))
        832 992 1024 1184 (UInt256.ofNat round) 12 13 1059
        (tail round rounds flag)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setup7Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, MixG.entryState, memory5, memory6, baseState, tail,
      hrun, hcode, jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_setup8 (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup8Path
        (MixG.finalState (baseState s (memory6 memory round))
          832 992 1024 1184 (UInt256.ofNat round) 12 13 1059
          (tail round rounds flag)) =
      some (MixG.entryState (baseState s (memory7 memory round))
        864 896 1056 1216 (UInt256.ofNat round) 14 15 1084
        (tail round rounds flag)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      setup8Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, MixG.entryState, memory6, memory7, baseState, tail,
      hrun, hcode, jumpDest96, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_increment (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hround : round < rounds.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath
        (MixG.finalState (baseState s (memory7 memory round))
          864 896 1056 1216 (UInt256.ofNat round) 14 15 1084
          (tail round rounds flag)) =
      some (loopState s (round + 1) rounds flag (memory8 memory round)) := by
  have hadd : UInt256.ofNat round + UInt256.ofNat 1 =
      UInt256.ofNat (round + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by
      exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hround) rounds.val.isLt)
  have hswap :
      [UInt256.ofNat (round + 1), UInt256.ofNat round, rounds, flag].exchange 0 1 =
        some [UInt256.ofNat round, UInt256.ofNat (round + 1), rounds, flag] := by
    rfl
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      incrementPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      MixG.finalState, loopState, memory7, memory8, baseState, tail,
      hrun, hcode, jumpDest877, hadd, hswap, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

end Challenge.Blake2f.Reference.Proofs.Bytecode.Round
