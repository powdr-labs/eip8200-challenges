import Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Counter and final-flag initialization

The two remaining little-endian inputs are loaded through the certified helper,
xored into `v[12..13]`, and the final flag conditionally complements `v[14]`.
The post-state is the invariant consumed by the compiled round driver.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def t0Word (input : ByteArray) : UInt256 := Initialization.decodedWord input 196
def t1Word (input : ByteArray) : UInt256 := Initialization.decodedWord input 204

def t0Memory (input : ByteArray) : ByteArray :=
  Initialization.storeWord (Initialization.constantsMemory input) 1152
    (UInt256.xor (MachineState.readWord (Initialization.constantsMemory input) 1152)
      (t0Word input))

def t1Memory (input : ByteArray) : ByteArray :=
  Initialization.storeWord (t0Memory input) 1184
    (UInt256.xor (MachineState.readWord (t0Memory input) 1184) (t1Word input))

def flaggedMemory (input : ByteArray) : ByteArray :=
  Initialization.storeWord (t1Memory input) 1216
    (UInt256.xor (MachineState.readWord (t1Memory input) 1216)
      (UInt256.ofNat 0xffffffffffffffff))

def finalMemory (input : ByteArray) : ByteArray :=
  if input[212]!.toNat = 0 then t1Memory input else flaggedMemory input

def t0CallState (input : ByteArray) : State :=
  { Initialization.constantsFinalState input with
    pc := UInt256.ofNat 4
    stack := [UInt256.ofNat 196, ⟨0⟩, UInt256.ofNat 821,
      Prelude.roundsWord input, Prelude.finalFlagWord input] }

def t0LoadedState (input : ByteArray) : State :=
  { Initialization.constantsFinalState input with
    pc := UInt256.ofNat 821
    stack := [t0Word input, Prelude.roundsWord input,
      Prelude.finalFlagWord input] }

def t0FinalState (input : ByteArray) : State :=
  { Initialization.constantsFinalState input with
    pc := UInt256.ofNat 831
    stack := [Prelude.roundsWord input, Prelude.finalFlagWord input]
    memory := t0Memory input }

def t1CallState (input : ByteArray) : State :=
  { t0FinalState input with
    pc := UInt256.ofNat 4
    stack := [UInt256.ofNat 204, ⟨0⟩, UInt256.ofNat 841,
      Prelude.roundsWord input, Prelude.finalFlagWord input] }

def t1LoadedState (input : ByteArray) : State :=
  { t0FinalState input with
    pc := UInt256.ofNat 841
    stack := [t1Word input, Prelude.roundsWord input,
      Prelude.finalFlagWord input] }

def flagEntryState (input : ByteArray) : State :=
  { t0FinalState input with
    pc := UInt256.ofNat 851
    stack := [Prelude.roundsWord input, Prelude.finalFlagWord input]
    memory := t1Memory input }

def flagMutationState (input : ByteArray) : State :=
  { flagEntryState input with pc := UInt256.ofNat 857 }

def flagJoinState (input : ByteArray) (memory : ByteArray) : State :=
  { flagEntryState input with pc := UInt256.ofNat 875, memory }

def roundLoopState (input : ByteArray) (round : Nat) (memory : ByteArray) : State :=
  { Initialization.constantsFinalState input with
    pc := UInt256.ofNat 878
    stack := [UInt256.ofNat round, Prelude.roundsWord input,
      Prelude.finalFlagWord input]
    memory
    activeWords := UInt256.ofNat 58 }

def roundEntryState (input : ByteArray) : State :=
  roundLoopState input 0 (finalMemory input)

def t0SetupPath := Artifact.locatedPath [401, 402, 403, 404, 405]
def t0StorePath := Artifact.locatedPath [406, 407, 408, 409, 410, 411]
def t1SetupPath := Artifact.locatedPath [412, 413, 414, 415, 416]
def t1StorePath := Artifact.locatedPath [417, 418, 419, 420, 421, 422]
def flagTestPath := Artifact.locatedPath [423, 424, 425, 426]
def flagMutationPath := Artifact.locatedPath [427, 428, 429, 430, 431, 432]
def flagFinishPath := Artifact.locatedPath [433, 434, 435]

private theorem jumpDest4 : Decode.isValidJumpDest referenceBytecode 4 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 2 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem jumpDest821 : Decode.isValidJumpDest referenceBytecode 821 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 406 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem jumpDest841 : Decode.isValidJumpDest referenceBytecode 841 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 417 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem ofNatAdd (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

theorem run_t0Setup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock t0SetupPath
      (Initialization.constantsFinalState input) = some (t0CallState input) := by
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      t0SetupPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Initialization.constantsFinalState, t0CallState, Prelude.finalState, initialState,
      jumpDest4, ofNatAdd, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_t0Store (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock t0StorePath
      (t0LoadedState input) = some (t0FinalState input) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      t0StorePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC, ofNatAdd,
      t0LoadedState, t0FinalState, t0Memory, Initialization.storeWord,
      Initialization.constantsFinalState, Prelude.finalState, initialState,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_t1Setup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock t1SetupPath
      (t0FinalState input) = some (t1CallState input) := by
  simp (config := { maxSteps := 300000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      t1SetupPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC, ofNatAdd,
      t0FinalState, t1CallState, Initialization.constantsFinalState,
      Prelude.finalState, initialState, jumpDest4,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_t1Store (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock t1StorePath
      (t1LoadedState input) = some (flagEntryState input) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      t1StorePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC, ofNatAdd,
      t1LoadedState, flagEntryState, t1Memory, Initialization.storeWord,
      t0FinalState, Initialization.constantsFinalState, Prelude.finalState, initialState,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_flagTestZero (input : ByteArray) (hflag : input[212]!.toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock flagTestPath
      (flagEntryState input) = some (flagJoinState input (t1Memory input)) := by
  have h875 := Artifact.referenceArtifact.isValidJumpDest_index 433 (by rfl)
  have h875' : Decode.isValidJumpDest referenceBytecode 875 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h875
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      flagTestPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC, ofNatAdd,
      flagEntryState, flagJoinState,
      Prelude.finalFlagWord, hflag, h875', t1Memory,
      t0FinalState, Initialization.constantsFinalState, Prelude.finalState, initialState,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isZero, UInt256.isTrue]

theorem run_flagTestOne (input : ByteArray) (hflag : input[212]!.toNat = 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock flagTestPath
      (flagEntryState input) = some (flagMutationState input) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      flagTestPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC, ofNatAdd,
      flagEntryState, flagMutationState,
      Prelude.finalFlagWord, hflag, t1Memory,
      t0FinalState, Initialization.constantsFinalState, Prelude.finalState, initialState,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isZero, UInt256.isTrue]

theorem run_flagMutation (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock flagMutationPath
      (flagMutationState input) = some (flagJoinState input (flaggedMemory input)) := by
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      flagMutationPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC, ofNatAdd,
      flagMutationState, flagJoinState, flagEntryState, flaggedMemory,
      t1Memory, Initialization.storeWord,
      t0FinalState, Initialization.constantsFinalState, Prelude.finalState, initialState,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_flagFinish (input : ByteArray) (memory : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock flagFinishPath
      (flagJoinState input memory) = some (roundLoopState input 0 memory) := by
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      flagFinishPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC, ofNatAdd,
      flagJoinState, roundLoopState, flagEntryState, t0FinalState,
      Initialization.constantsFinalState, Prelude.finalState, initialState,
      hzero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

end Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization
