import Challenge.Blake2f.Reference.Proofs.Bytecode.LoadLE64
import Challenge.Blake2f.Reference.Proofs.Bytecode.Prelude
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Meter
import Mathlib.Tactic.IntervalCases

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Valid-input memory initialization

This module composes the already-certified `loadLE64` helper with the three
compiled decoding/copy loops and the fixed IV/sigma stores.  State definitions
are parameterized by loop progress so candidate proofs can reuse the same
memory invariant and gas decomposition.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def storeWord (memory : ByteArray) (offset : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

def decodedWord (input : ByteArray) (offset : Nat) : UInt256 :=
  LoadLE64.accumulator (MachineState.readWord input offset) 8

/-- Decode `count` little-endian calldata words into 32-byte memory slots. -/
def decodeWords (input : ByteArray) (calldataBase memoryBase : Nat) :
    Nat → ByteArray → ByteArray
  | 0, memory => memory
  | count + 1, memory =>
      storeWord (decodeWords input calldataBase memoryBase count memory)
        (memoryBase + 32 * count)
        (decodedWord input (calldataBase + 8 * count))

def hMemory (input : ByteArray) (count : Nat) : ByteArray :=
  decodeWords input 4 0 count ByteArray.empty

def hLoopState (input : ByteArray) (count : Nat) : State :=
  { Prelude.finalState input with
    pc := UInt256.ofNat 371
    stack := [UInt256.ofNat count, Prelude.roundsWord input,
      Prelude.finalFlagWord input]
    memory := hMemory input count
    activeWords := UInt256.ofNat count }

def hContinuePath := Artifact.locatedPath
  [258, 259, 260, 261, 262, 263,
   264, 265, 266, 267, 268, 269, 270, 271, 272]

def hStorePath := Artifact.locatedPath
  [273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 257]

def hExitPath := Artifact.locatedPath
  [258, 259, 260, 261, 262, 263, 285, 286, 287, 288]

def hCallState (input : ByteArray) (count : Nat) : State :=
  { hLoopState input count with
    pc := UInt256.ofNat 4
    stack := [UInt256.ofNat (4 + 8 * count), ⟨0⟩, UInt256.ofNat 395,
      UInt256.ofNat count, Prelude.roundsWord input,
      Prelude.finalFlagWord input] }

def hLoadedState (input : ByteArray) (count : Nat) : State :=
  { hLoopState input count with
    pc := UInt256.ofNat 395
    stack := [decodedWord input (4 + 8 * count), UInt256.ofNat count,
      Prelude.roundsWord input, Prelude.finalFlagWord input] }

def mLoopState (input : ByteArray) (count : Nat) : State :=
  { Prelude.finalState input with
    pc := UInt256.ofNat 415
    stack := [UInt256.ofNat count, Prelude.roundsWord input,
      Prelude.finalFlagWord input]
    memory := decodeWords input 68 256 count (hMemory input 8)
    activeWords := UInt256.ofNat (8 + count) }

def mContinuePath := Artifact.locatedPath
  [289, 290, 291, 292, 293, 294,
   295, 296, 297, 298, 299, 300, 301, 302, 303]

def mStorePath := Artifact.locatedPath
  [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315,
   316, 317, 288]

def mExitPath := Artifact.locatedPath
  [289, 290, 291, 292, 293, 294, 318, 319, 320, 321]

def mCallState (input : ByteArray) (count : Nat) : State :=
  { mLoopState input count with
    pc := UInt256.ofNat 4
    stack := [UInt256.ofNat (68 + 8 * count), ⟨0⟩, UInt256.ofNat 439,
      UInt256.ofNat count, Prelude.roundsWord input,
      Prelude.finalFlagWord input] }

def mLoadedState (input : ByteArray) (count : Nat) : State :=
  { mLoopState input count with
    pc := UInt256.ofNat 439
    stack := [decodedWord input (68 + 8 * count), UInt256.ofNat count,
      Prelude.roundsWord input, Prelude.finalFlagWord input] }

def mMemory (input : ByteArray) : ByteArray :=
  decodeWords input 68 256 16 (hMemory input 8)

def copyHToV : Nat → ByteArray → ByteArray
  | 0, memory => memory
  | count + 1, memory =>
      let prior := copyHToV count memory
      storeWord prior (768 + 32 * count)
        (MachineState.readWord prior (32 * count))

def vMemory (input : ByteArray) (count : Nat) : ByteArray :=
  copyHToV count (mMemory input)

def vLoopState (input : ByteArray) (count : Nat) : State :=
  { Prelude.finalState input with
    pc := UInt256.ofNat 463
    stack := [UInt256.ofNat count, Prelude.roundsWord input,
      Prelude.finalFlagWord input]
    memory := vMemory input count
    activeWords := UInt256.ofNat (24 + count) }

def vContinuePath := Artifact.locatedPath
  [322, 323, 324, 325, 326, 327]

def vBodyPath := Artifact.locatedPath
  [328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339,
   340, 341, 342, 343, 344, 321]

def vExitPath := Artifact.locatedPath
  [322, 323, 324, 325, 326, 327, 345, 346]

def vBodyState (input : ByteArray) (count : Nat) : State :=
  { vLoopState input count with pc := UInt256.ofNat 472 }

def constantsEntryState (input : ByteArray) : State :=
  { Prelude.finalState input with
    pc := UInt256.ofNat 498
    stack := [Prelude.roundsWord input, Prelude.finalFlagWord input]
    memory := vMemory input 8
    activeWords := UInt256.ofNat 32 }

def fixedStores : List (Nat × Nat) :=
  [(1024, 0x6a09e667f3bcc908),
   (1056, 0xbb67ae8584caa73b),
   (1088, 0x3c6ef372fe94f82b),
   (1120, 0xa54ff53a5f1d36f1),
   (1152, 0x510e527fade682d1),
   (1184, 0x9b05688c2b3e6c1f),
   (1216, 0x1f83d9abfb41bd6b),
   (1248, 0x5be0cd19137e2179),
   (1536, 0x000102030405060708090a0b0c0d0e0f),
   (1568, 0x0e0a0408090f0d06010c00020b070503),
   (1600, 0x0b080c0005020f0d0a0e030607010904),
   (1632, 0x070903010d0c0b0e0206050a04000f08),
   (1664, 0x0900050702040a0f0e010b0c0608030d),
   (1696, 0x020c060a000b0803040d07050f0e0109),
   (1728, 0x0c05010f0e0d040a000706030902080b),
   (1760, 0x0d0b070e0c01030905000f040806020a),
   (1792, 0x060f0e090b0300080c020d0701040a05),
   (1824, 0x0a020804070601050f0b090e030c0d00)]

def applyFixedStore (memory : ByteArray) (entry : Nat × Nat) : ByteArray :=
  storeWord memory entry.1 (UInt256.ofNat entry.2)

def constantsMemory (input : ByteArray) : ByteArray :=
  fixedStores.foldl applyFixedStore (vMemory input 8)

def constantsFinalState (input : ByteArray) : State :=
  { Prelude.finalState input with
    pc := UInt256.ofNat 811
    stack := [Prelude.roundsWord input, Prelude.finalFlagWord input]
    memory := constantsMemory input
    activeWords := UInt256.ofNat 58 }

def constantsPath := Artifact.locatedPath
  [347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358,
   359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370,
   371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382,
   383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394,
   395, 396, 397, 398, 399, 400]

theorem hLoopState_zero (input : ByteArray) :
    hLoopState input 0 = Prelude.finalState input := by
  unfold hLoopState hMemory decodeWords Prelude.finalState
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by decide]
  rfl

theorem run_hContinue (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock hContinuePath
        (hLoopState input count) = some (hCallState input count) := by
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift : UInt256.shiftLeft (UInt256.ofNat count) (UInt256.ofNat 3) =
      UInt256.ofNat (8 * count) := by
    simpa [Nat.mul_comm] using
      (Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := count) (shift := 3) (by omega) (by omega) (by omega))
  have hoff : UInt256.ofNat (8 * count) + UInt256.ofNat 4 =
      UInt256.ofNat (4 + 8 * count) := by
    simpa [Nat.add_comm] using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 8 * count) (b := 4) (by omega)
  have hoff' : UInt256.ofNat 4 + UInt256.ofNat (8 * count) =
      UInt256.ofNat (4 + 8 * count) := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h4 := Artifact.referenceArtifact.isValidJumpDest_index 2 (by rfl)
  have h4' : Decode.isValidJumpDest referenceBytecode 4 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h4
  have hpc373 : UInt256.ofNat 371 + UInt256.ofNat 2 = UInt256.ofNat 373 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 371) (b := 2) (by norm_num)
  have hpc379 : UInt256.ofNat 376 + UInt256.ofNat 3 = UInt256.ofNat 379 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 376) (b := 3) (by norm_num)
  have hpc383 : UInt256.ofNat 380 + UInt256.ofNat 3 = UInt256.ofNat 383 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 380) (b := 3) (by norm_num)
  have hpc387 : UInt256.ofNat 385 + UInt256.ofNat 2 = UInt256.ofNat 387 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 385) (b := 2) (by norm_num)
  have hpc390 : UInt256.ofNat 388 + UInt256.ofNat 2 = UInt256.ofNat 390 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 388) (b := 2) (by norm_num)
  have hpc394 : UInt256.ofNat 391 + UInt256.ofNat 3 = UInt256.ofNat 394 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 391) (b := 3) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hContinuePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hLoopState, hCallState, Prelude.finalState, initialState,
      hcount, hcountWord, hshift, hoff, hoff', h4', hpc373, hpc379, hpc383,
      hpc387, hpc390, hpc394,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_hStore (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock hStorePath
        (hLoadedState input count) = some (hLoopState input (count + 1)) := by
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift : UInt256.shiftLeft (UInt256.ofNat count) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * count) := by
    simpa [Nat.mul_comm] using
      (Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := count) (shift := 5) (by omega) (by omega) (by omega))
  have hadd : UInt256.ofNat count + UInt256.ofNat 1 =
      UInt256.ofNat (count + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hcountActive : (UInt256.ofNat count).toNat = count := hcountWord
  have h32count : (UInt256.ofNat (32 * count)).toNat = 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hactiveAfter : MachineState.activeWordsAfter count (32 * count) 32 =
      count + 1 := by
    simp [MachineState.activeWordsAfter]
    rw [show 32 * count + 31 = 31 + 32 * count by omega,
      Nat.add_mul_div_left 31 count (y := 32) (by norm_num)]
    norm_num
  have hceil : (32 * count + 31) / 32 + 1 = count + 1 := by
    rw [show 32 * count + 31 = 31 + 32 * count by omega,
      Nat.add_mul_div_left 31 count (y := 32) (by norm_num)]
    norm_num
  have hswap :
      [UInt256.ofNat (count + 1), UInt256.ofNat count,
        Prelude.roundsWord input, Prelude.finalFlagWord input].exchange 0 1 =
      some [UInt256.ofNat count, UInt256.ofNat (count + 1),
        Prelude.roundsWord input, Prelude.finalFlagWord input] := by
    rfl
  have h370 := Artifact.referenceArtifact.isValidJumpDest_index 257 (by rfl)
  have h370' : Decode.isValidJumpDest referenceBytecode 370 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h370
  have hpc399 : UInt256.ofNat 397 + UInt256.ofNat 2 = UInt256.ofNat 399 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 397) (b := 2) (by norm_num)
  have hpc403 : UInt256.ofNat 401 + UInt256.ofNat 2 = UInt256.ofNat 403 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 401) (b := 2) (by norm_num)
  have hpc410 : UInt256.ofNat 407 + UInt256.ofNat 3 = UInt256.ofNat 410 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 407) (b := 3) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hStorePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hLoadedState, hLoopState, hMemory, decodeWords, storeWord, decodedWord,
      Prelude.finalState, initialState, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter,
      hcount, hcountWord, hshift, hadd, hcountActive, h32count, hactiveAfter,
      hceil,
      hswap, h370', hpc399, hpc403, hpc410,
      Nat.add_assoc, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

theorem run_hExit (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hExitPath
        (hLoopState input 8) = some (mLoopState input 0) := by
  have h411 := Artifact.referenceArtifact.isValidJumpDest_index 285 (by rfl)
  have h411' : Decode.isValidJumpDest referenceBytecode 411 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h411
  have hpc373 : UInt256.ofNat 371 + UInt256.ofNat 2 = UInt256.ofNat 373 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 371) (b := 2) (by norm_num)
  have hpc379 : UInt256.ofNat 376 + UInt256.ofNat 3 = UInt256.ofNat 379 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 376) (b := 3) (by norm_num)
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hExitPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      hLoopState, mLoopState, hMemory, decodeWords, Prelude.finalState,
      initialState, h411', hpc373, hpc379, hzero, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_mContinue (input : ByteArray) (count : Nat) (hcount : count < 16) :
    Challenge.EvmProof.Stepper.runLocatedBlock mContinuePath
        (mLoopState input count) = some (mCallState input count) := by
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift : UInt256.shiftLeft (UInt256.ofNat count) (UInt256.ofNat 3) =
      UInt256.ofNat (8 * count) := by
    simpa [Nat.mul_comm] using
      (Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := count) (shift := 3) (by omega) (by omega) (by omega))
  have hoff : UInt256.ofNat 68 + UInt256.ofNat (8 * count) =
      UInt256.ofNat (68 + 8 * count) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h4 := Artifact.referenceArtifact.isValidJumpDest_index 2 (by rfl)
  have h4' : Decode.isValidJumpDest referenceBytecode 4 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h4
  have hpc417 : UInt256.ofNat 415 + UInt256.ofNat 2 = UInt256.ofNat 417 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 415) (b := 2) (by norm_num)
  have hpc423 : UInt256.ofNat 420 + UInt256.ofNat 3 = UInt256.ofNat 423 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 420) (b := 3) (by norm_num)
  have hpc427 : UInt256.ofNat 424 + UInt256.ofNat 3 = UInt256.ofNat 427 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 424) (b := 3) (by norm_num)
  have hpc431 : UInt256.ofNat 429 + UInt256.ofNat 2 = UInt256.ofNat 431 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 429) (b := 2) (by norm_num)
  have hpc434 : UInt256.ofNat 432 + UInt256.ofNat 2 = UInt256.ofNat 434 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 432) (b := 2) (by norm_num)
  have hpc438 : UInt256.ofNat 435 + UInt256.ofNat 3 = UInt256.ofNat 438 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 435) (b := 3) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mContinuePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      mLoopState, mCallState, Prelude.finalState, initialState,
      hcount, hcountWord, hshift, hoff, h4', hpc417, hpc423, hpc427,
      hpc431, hpc434, hpc438, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_mStore (input : ByteArray) (count : Nat) (hcount : count < 16) :
    Challenge.EvmProof.Stepper.runLocatedBlock mStorePath
        (mLoadedState input count) = some (mLoopState input (count + 1)) := by
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift : UInt256.shiftLeft (UInt256.ofNat count) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * count) := by
    simpa [Nat.mul_comm] using
      (Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := count) (shift := 5) (by omega) (by omega) (by omega))
  have hoff : UInt256.ofNat 256 + UInt256.ofNat (32 * count) =
      UInt256.ofNat (256 + 32 * count) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hoffNat : (UInt256.ofNat (256 + 32 * count)).toNat =
      256 + 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd : UInt256.ofNat count + UInt256.ofNat 1 =
      UInt256.ofNat (count + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hactiveNat : (UInt256.ofNat (8 + count)).toNat = 8 + count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hactiveAfter :
      MachineState.activeWordsAfter (8 + count) (256 + 32 * count) 32 =
        8 + (count + 1) := by
    simp [MachineState.activeWordsAfter]
    rw [show 256 + 32 * count + 31 = 31 + 32 * (8 + count) by omega,
      Nat.add_mul_div_left 31 (8 + count) (y := 32) (by norm_num)]
    norm_num
    omega
  have hceil : (256 + 32 * count + 31) / 32 + 1 = 8 + (count + 1) := by
    rw [show 256 + 32 * count + 31 = 31 + 32 * (8 + count) by omega,
      Nat.add_mul_div_left 31 (8 + count) (y := 32) (by norm_num)]
    norm_num
    omega
  have hceil' : (256 + (32 * count + 31)) / 32 + 1 =
      8 + (count + 1) := by
    rw [show 256 + (32 * count + 31) = 256 + 32 * count + 31 by omega]
    exact hceil
  have hswap :
      [UInt256.ofNat (count + 1), UInt256.ofNat count,
        Prelude.roundsWord input, Prelude.finalFlagWord input].exchange 0 1 =
      some [UInt256.ofNat count, UInt256.ofNat (count + 1),
        Prelude.roundsWord input, Prelude.finalFlagWord input] := by rfl
  have h414 := Artifact.referenceArtifact.isValidJumpDest_index 288 (by rfl)
  have h414' : Decode.isValidJumpDest referenceBytecode 414 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h414
  have hpc443 : UInt256.ofNat 441 + UInt256.ofNat 2 = UInt256.ofNat 443 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 441) (b := 2) (by norm_num)
  have hpc447 : UInt256.ofNat 444 + UInt256.ofNat 3 = UInt256.ofNat 447 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 444) (b := 3) (by norm_num)
  have hpc451 : UInt256.ofNat 449 + UInt256.ofNat 2 = UInt256.ofNat 451 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 449) (b := 2) (by norm_num)
  have hpc458 : UInt256.ofNat 455 + UInt256.ofNat 3 = UInt256.ofNat 458 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 455) (b := 3) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mStorePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      mLoadedState, mLoopState, decodeWords, storeWord, decodedWord,
      Prelude.finalState, initialState, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter,
      hcount, hcountWord, hshift, hoff, hoffNat, hadd, hactiveNat,
      hactiveAfter, hceil, hceil', hswap, h414', hpc443, hpc447, hpc451,
      hpc458,
      Nat.add_assoc, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

theorem run_mExit (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock mExitPath
        (mLoopState input 16) = some (vLoopState input 0) := by
  have h459 := Artifact.referenceArtifact.isValidJumpDest_index 318 (by rfl)
  have h459' : Decode.isValidJumpDest referenceBytecode 459 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h459
  have hpc417 : UInt256.ofNat 415 + UInt256.ofNat 2 = UInt256.ofNat 417 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 415) (b := 2) (by norm_num)
  have hpc423 : UInt256.ofNat 420 + UInt256.ofNat 3 = UInt256.ofNat 423 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 420) (b := 3) (by norm_num)
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      mExitPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      mLoopState, vLoopState, vMemory, copyHToV, mMemory,
      Prelude.finalState, initialState,
      h459', hpc417, hpc423, hzero, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_vContinue (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock vContinuePath
        (vLoopState input count) = some (vBodyState input count) := by
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpc465 : UInt256.ofNat 463 + UInt256.ofNat 2 = UInt256.ofNat 465 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 463) (b := 2) (by norm_num)
  have hpc471 : UInt256.ofNat 468 + UInt256.ofNat 3 = UInt256.ofNat 471 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 468) (b := 3) (by norm_num)
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      vContinuePath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      vLoopState, vBodyState, Prelude.finalState, initialState,
      hcount, hcountWord, hpc465, hpc471, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_vBody (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock vBodyPath
        (vBodyState input count) = some (vLoopState input (count + 1)) := by
  have hcountWord : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift : UInt256.shiftLeft (UInt256.ofNat count) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * count) := by
    simpa [Nat.mul_comm] using
      (Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := count) (shift := 5) (by omega) (by omega) (by omega))
  have hsourceNat : (UInt256.ofNat (32 * count)).toNat = 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdest : UInt256.ofNat 768 + UInt256.ofNat (32 * count) =
      UInt256.ofNat (768 + 32 * count) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdestNat : (UInt256.ofNat (768 + 32 * count)).toNat =
      768 + 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd : UInt256.ofNat count + UInt256.ofNat 1 =
      UInt256.ofNat (count + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hactiveNat : (UInt256.ofNat (24 + count)).toNat = 24 + count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hceil : (768 + (32 * count + 31)) / 32 + 1 = 24 + (count + 1) := by
    rw [show 768 + (32 * count + 31) = 31 + 32 * (24 + count) by omega,
      Nat.add_mul_div_left 31 (24 + count) (y := 32) (by norm_num)]
    norm_num
    omega
  have hswap :
      [UInt256.ofNat (count + 1), UInt256.ofNat count,
        Prelude.roundsWord input, Prelude.finalFlagWord input].exchange 0 1 =
      some [UInt256.ofNat count, UInt256.ofNat (count + 1),
        Prelude.roundsWord input, Prelude.finalFlagWord input] := by rfl
  have h462 := Artifact.referenceArtifact.isValidJumpDest_index 321 (by rfl)
  have h462' : Decode.isValidJumpDest referenceBytecode 462 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h462
  have hpc475 : UInt256.ofNat 473 + UInt256.ofNat 2 = UInt256.ofNat 475 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 473) (b := 2) (by norm_num)
  have hpc480 : UInt256.ofNat 478 + UInt256.ofNat 2 = UInt256.ofNat 480 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 478) (b := 2) (by norm_num)
  have hpc484 : UInt256.ofNat 481 + UInt256.ofNat 3 = UInt256.ofNat 484 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 481) (b := 3) (by norm_num)
  have hpc488 : UInt256.ofNat 486 + UInt256.ofNat 2 = UInt256.ofNat 488 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 486) (b := 2) (by norm_num)
  have hpc495 : UInt256.ofNat 492 + UInt256.ofNat 3 = UInt256.ofNat 495 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 492) (b := 3) (by norm_num)
  simp (config := { maxSteps := 700000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      vBodyPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      vBodyState, vLoopState, vMemory, copyHToV, storeWord,
      Prelude.finalState, initialState, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter,
      hcount, hcountWord, hshift, hsourceNat, hdest, hdestNat, hadd,
      hactiveNat, hceil, hswap, h462', hpc475, hpc480, hpc484, hpc488,
      hpc495, Nat.add_assoc, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

theorem run_vExit (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock vExitPath
        (vLoopState input 8) = some (constantsEntryState input) := by
  have h496 := Artifact.referenceArtifact.isValidJumpDest_index 345 (by rfl)
  have h496' : Decode.isValidJumpDest referenceBytecode 496 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h496
  have hpc465 : UInt256.ofNat 463 + UInt256.ofNat 2 = UInt256.ofNat 465 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 463) (b := 2) (by norm_num)
  have hpc471 : UInt256.ofNat 468 + UInt256.ofNat 3 = UInt256.ofNat 471 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 468) (b := 3) (by norm_num)
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      vExitPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      vLoopState, constantsEntryState, Prelude.finalState, initialState,
      h496', hpc465, hpc471, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_constants (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock constantsPath
        (constantsEntryState input) = some (constantsFinalState input) := by
  have ofNatAdd (a b : Nat) (h : a + b < 2 ^ 256) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat h
  simp (config := { maxSteps := 2000000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      constantsPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      constantsEntryState, constantsFinalState, constantsMemory,
      fixedStores, applyFixedStore, storeWord,
      Prelude.finalState, initialState, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter, ofNatAdd,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

private def gasStepsBlock
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps a b := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact hresult
  · exact hrun
  · exact hnp

@[simp] private theorem gasStepsBlock_cost
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    (gasStepsBlock path hresult hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost path a := rfl

private theorem hState_code (input : ByteArray) (count : Nat) :
    (hLoopState input count).executionEnv.code = referenceBytecode := by
  rfl

private theorem hState_fork (input : ByteArray) (count : Nat) :
    (hLoopState input count).fork = .Osaka := by
  rfl

private theorem hState_running (input : ByteArray) (count : Nat) :
    (hLoopState input count).halt = .Running := by
  rfl

private theorem hState_notPrecompile (input : ByteArray) (count : Nat) :
    Precompile.isPrecompileWithConfig
      (hLoopState input count).executionEnv.precompileConfig
      (hLoopState input count).executionEnv.fork
      (hLoopState input count).executionEnv.codeAddr = false := by
  exact deployAddress_not_precompile

private theorem return395_valid :
    Decode.isValidJumpDest referenceBytecode 395 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 273 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

def hIterationGasSteps (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.GasSteps (hLoopState input count)
      (hLoopState input (count + 1)) := by
  have gcontinue := gasStepsBlock hContinuePath (run_hContinue input count hcount)
    (hState_code input count) (hState_fork input count)
    (hState_running input count) (hState_notPrecompile input count)
  have gload := LoadLE64.gasSteps (hLoopState input count)
    (UInt256.ofNat (4 + 8 * count)) (UInt256.ofNat 395)
    [UInt256.ofNat count, Prelude.roundsWord input, Prelude.finalFlagWord input]
    (by simp) (hState_code input count) (hState_fork input count)
    (hState_running input count) (hState_notPrecompile input count)
    return395_valid
  have gstore := gasStepsBlock hStorePath (run_hStore input count hcount)
    (by simpa [hLoadedState] using hState_code input count)
    (by simpa [hLoadedState, State.fork] using hState_fork input count)
    (by simpa [hLoadedState] using hState_running input count)
    (by simpa [hLoadedState] using hState_notPrecompile input count)
  have hoffNat : (UInt256.ofNat (4 + 8 * count)).toNat = 4 + 8 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Challenge.EvmProof.GasSteps.cast
    (gcontinue.trans ((Challenge.EvmProof.GasSteps.cast gload rfl (by
      simp [LoadLE64.finalState, hLoadedState, hCallState, decodedWord,
        hLoopState, Prelude.finalState, initialState, hoffNat])).trans gstore))
    rfl rfl

theorem hContinue_cost (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost hContinuePath
      (hLoopState input count) = 56 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    hContinuePath 56 (run_hContinue input count hcount) rfl
    (by
      intro located hlocated
      have hall : hContinuePath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  have hcountNat : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simpa [hLoopState, hCallState, hcountNat] using hpotential

theorem hStore_cost (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost hStorePath
      (hLoadedState input count) = 42 := by
  have hcountNat : (UInt256.ofNat count).toNat = count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnextNat : (UInt256.ofNat (count + 1)).toNat = count + 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    hStorePath 39 (run_hStore input count hcount) rfl
    (by
      intro located hlocated
      have hall : hStorePath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  have hinActive : (hLoadedState input count).activeWords.toNat = count := by
    simp [hLoadedState, hLoopState, hcountNat]
  have houtActive : (hLoopState input (count + 1)).activeWords.toNat =
      count + 1 := by
    simp [hLoopState, hnextNat]
  rw [hinActive, houtActive] at hpotential
  simp only [MachineState.memCost] at hpotential
  interval_cases count <;> norm_num at hpotential ⊢ <;> omega

@[simp] theorem hIterationGasSteps_cost (input : ByteArray) (count : Nat)
    (hcount : count < 8) :
    (hIterationGasSteps input count hcount).cost = 815 := by
  unfold hIterationGasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [hContinue_cost input count hcount]
  rw [LoadLE64.gasSteps_cost]
  rw [hStore_cost input count hcount]

def hLoopGasSteps (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Prelude.finalState input) (mLoopState input 0) := by
  have gloop : Challenge.EvmProof.GasSteps (hLoopState input 0)
      (hLoopState input 8) :=
    Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
      (I := hLoopState input)
      (fun i hi => hIterationGasSteps input i hi)
  have gexit := gasStepsBlock hExitPath (run_hExit input)
    (hState_code input 8) (hState_fork input 8)
    (hState_running input 8) (hState_notPrecompile input 8)
  exact Challenge.EvmProof.GasSteps.cast (gloop.trans gexit)
    (hLoopState_zero input) rfl

theorem hExit_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost hExitPath
      (hLoopState input 8) = 31 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    hExitPath 31 (run_hExit input) rfl
    (by
      intro located hlocated
      have hall : hExitPath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  simpa [hLoopState, mLoopState] using hpotential

@[simp] theorem hLoopGasSteps_cost (input : ByteArray) :
    (hLoopGasSteps input).cost = 6551 := by
  unfold hLoopGasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [hExit_cost input]
  have hloop := Challenge.EvmProof.GasSteps.iterateBounded_cost_of_const
    8 815
    (fun i hi => hIterationGasSteps input i hi)
    (fun i hi => hIterationGasSteps_cost input i hi)
  rw [hloop]

private theorem mState_code (input : ByteArray) (count : Nat) :
    (mLoopState input count).executionEnv.code = referenceBytecode := by rfl

private theorem mState_fork (input : ByteArray) (count : Nat) :
    (mLoopState input count).fork = .Osaka := by rfl

private theorem mState_running (input : ByteArray) (count : Nat) :
    (mLoopState input count).halt = .Running := by rfl

private theorem mState_notPrecompile (input : ByteArray) (count : Nat) :
    Precompile.isPrecompileWithConfig
      (mLoopState input count).executionEnv.precompileConfig
      (mLoopState input count).executionEnv.fork
      (mLoopState input count).executionEnv.codeAddr = false := by
  exact deployAddress_not_precompile

private theorem return439_valid :
    Decode.isValidJumpDest referenceBytecode 439 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 304 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

def mIterationGasSteps (input : ByteArray) (count : Nat) (hcount : count < 16) :
    Challenge.EvmProof.GasSteps (mLoopState input count)
      (mLoopState input (count + 1)) := by
  have gcontinue := gasStepsBlock mContinuePath (run_mContinue input count hcount)
    (mState_code input count) (mState_fork input count)
    (mState_running input count) (mState_notPrecompile input count)
  have gload := LoadLE64.gasSteps (mLoopState input count)
    (UInt256.ofNat (68 + 8 * count)) (UInt256.ofNat 439)
    [UInt256.ofNat count, Prelude.roundsWord input, Prelude.finalFlagWord input]
    (by simp) (mState_code input count) (mState_fork input count)
    (mState_running input count) (mState_notPrecompile input count)
    return439_valid
  have gstore := gasStepsBlock mStorePath (run_mStore input count hcount)
    (by simpa [mLoadedState] using mState_code input count)
    (by simpa [mLoadedState, State.fork] using mState_fork input count)
    (by simpa [mLoadedState] using mState_running input count)
    (by simpa [mLoadedState] using mState_notPrecompile input count)
  have hoffNat : (UInt256.ofNat (68 + 8 * count)).toNat = 68 + 8 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Challenge.EvmProof.GasSteps.cast
    (gcontinue.trans ((Challenge.EvmProof.GasSteps.cast gload rfl (by
      simp [LoadLE64.finalState, mLoadedState, mCallState, decodedWord,
        mLoopState, Prelude.finalState, initialState, hoffNat])).trans gstore))
    rfl rfl

theorem mContinue_cost (input : ByteArray) (count : Nat) (hcount : count < 16) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost mContinuePath
      (mLoopState input count) = 56 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mContinuePath 56 (run_mContinue input count hcount) rfl
    (by
      intro located hlocated
      have hall : mContinuePath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  have hactiveNat : (UInt256.ofNat (8 + count)).toNat = 8 + count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simpa [mLoopState, mCallState, hactiveNat] using hpotential

theorem mStore_cost_potential (input : ByteArray) (count : Nat)
    (hcount : count < 16) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost mStorePath
        (mLoadedState input count) + MachineState.memCost (8 + count) =
      45 + MachineState.memCost (8 + (count + 1)) := by
  have hactiveNat : (UInt256.ofNat (8 + count)).toNat = 8 + count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnextNat : (UInt256.ofNat (8 + (count + 1))).toNat =
      8 + (count + 1) := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mStorePath 45 (run_mStore input count hcount) rfl
    (by
      intro located hlocated
      have hall : mStorePath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  have hinActive : (mLoadedState input count).activeWords.toNat = 8 + count := by
    simp [mLoadedState, mLoopState, hactiveNat]
  have houtActive : (mLoopState input (count + 1)).activeWords.toNat =
      8 + (count + 1) := by
    simp [mLoopState, hnextNat]
  simpa [hinActive, houtActive] using hpotential

theorem mIterationGasSteps_cost_potential (input : ByteArray) (count : Nat)
    (hcount : count < 16) :
    (mIterationGasSteps input count hcount).cost + MachineState.memCost (8 + count) =
      818 + MachineState.memCost (8 + (count + 1)) := by
  unfold mIterationGasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [mContinue_cost input count hcount]
  rw [LoadLE64.gasSteps_cost]
  have hstore := mStore_cost_potential input count hcount
  omega

def mLoopGasSteps (input : ByteArray) :
    Challenge.EvmProof.GasSteps (mLoopState input 0) (vLoopState input 0) := by
  have gloop : Challenge.EvmProof.GasSteps (mLoopState input 0)
      (mLoopState input 16) :=
    Challenge.EvmProof.GasSteps.iterateBounded (count := 16)
      (I := mLoopState input)
      (fun i hi => mIterationGasSteps input i hi)
  have gexit := gasStepsBlock mExitPath (run_mExit input)
    (mState_code input 16) (mState_fork input 16)
    (mState_running input 16) (mState_notPrecompile input 16)
  exact gloop.trans gexit

theorem mExit_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost mExitPath
      (mLoopState input 16) = 31 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mExitPath 31 (run_mExit input) rfl
    (by
      intro located hlocated
      have hall : mExitPath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  simpa [mLoopState, vLoopState] using hpotential

@[simp] theorem mLoopGasSteps_cost (input : ByteArray) :
    (mLoopGasSteps input).cost = 13168 := by
  unfold mLoopGasSteps
  simp only [Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [mExit_cost input]
  have hloop := Challenge.EvmProof.GasSteps.iterateBounded_cost_potential_eq
    16 818 (fun i => MachineState.memCost (8 + i))
    (fun i hi => mIterationGasSteps input i hi)
    (fun i hi => mIterationGasSteps_cost_potential input i hi)
  norm_num [MachineState.memCost] at hloop ⊢
  omega

private theorem vState_code (input : ByteArray) (count : Nat) :
    (vLoopState input count).executionEnv.code = referenceBytecode := by rfl

private theorem vState_fork (input : ByteArray) (count : Nat) :
    (vLoopState input count).fork = .Osaka := by rfl

private theorem vState_running (input : ByteArray) (count : Nat) :
    (vLoopState input count).halt = .Running := by rfl

private theorem vState_notPrecompile (input : ByteArray) (count : Nat) :
    Precompile.isPrecompileWithConfig
      (vLoopState input count).executionEnv.precompileConfig
      (vLoopState input count).executionEnv.fork
      (vLoopState input count).executionEnv.codeAddr = false := by
  exact deployAddress_not_precompile

def vIterationGasSteps (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.GasSteps (vLoopState input count)
      (vLoopState input (count + 1)) := by
  have gcontinue := gasStepsBlock vContinuePath (run_vContinue input count hcount)
    (vState_code input count) (vState_fork input count)
    (vState_running input count) (vState_notPrecompile input count)
  have gbody := gasStepsBlock vBodyPath (run_vBody input count hcount)
    (by simpa [vBodyState] using vState_code input count)
    (by simpa [vBodyState, State.fork] using vState_fork input count)
    (by simpa [vBodyState] using vState_running input count)
    (by simpa [vBodyState] using vState_notPrecompile input count)
  exact gcontinue.trans gbody

theorem vContinue_cost (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost vContinuePath
      (vLoopState input count) = 25 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    vContinuePath 25 (run_vContinue input count hcount) rfl
    (by
      intro located hlocated
      have hall : vContinuePath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  have hactiveNat : (UInt256.ofNat (24 + count)).toNat = 24 + count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simpa [vLoopState, vBodyState, hactiveNat] using hpotential

theorem vBody_cost_potential (input : ByteArray) (count : Nat)
    (hcount : count < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost vBodyPath
        (vBodyState input count) + MachineState.memCost (24 + count) =
      56 + MachineState.memCost (24 + (count + 1)) := by
  have hactiveNat : (UInt256.ofNat (24 + count)).toNat = 24 + count := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnextNat : (UInt256.ofNat (24 + (count + 1))).toNat =
      24 + (count + 1) := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    vBodyPath 56 (run_vBody input count hcount) rfl
    (by
      intro located hlocated
      have hall : vBodyPath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  have hinActive : (vBodyState input count).activeWords.toNat = 24 + count := by
    simp [vBodyState, vLoopState, hactiveNat]
  have houtActive : (vLoopState input (count + 1)).activeWords.toNat =
      24 + (count + 1) := by simp [vLoopState, hnextNat]
  simpa [hinActive, houtActive] using hpotential

theorem vIterationGasSteps_cost_potential (input : ByteArray) (count : Nat)
    (hcount : count < 8) :
    (vIterationGasSteps input count hcount).cost + MachineState.memCost (24 + count) =
      81 + MachineState.memCost (24 + (count + 1)) := by
  unfold vIterationGasSteps
  simp only [Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [vContinue_cost input count hcount]
  have hbody := vBody_cost_potential input count hcount
  omega

def vLoopGasSteps (input : ByteArray) :
    Challenge.EvmProof.GasSteps (vLoopState input 0) (constantsEntryState input) := by
  have gloop : Challenge.EvmProof.GasSteps (vLoopState input 0)
      (vLoopState input 8) :=
    Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
      (I := vLoopState input)
      (fun i hi => vIterationGasSteps input i hi)
  have gexit := gasStepsBlock vExitPath (run_vExit input)
    (vState_code input 8) (vState_fork input 8)
    (vState_running input 8) (vState_notPrecompile input 8)
  exact gloop.trans gexit

theorem vExit_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost vExitPath
      (vLoopState input 8) = 28 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    vExitPath 28 (run_vExit input) rfl
    (by
      intro located hlocated
      have hall : vExitPath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  simpa [vLoopState, constantsEntryState] using hpotential

@[simp] theorem vLoopGasSteps_cost (input : ByteArray) :
    (vLoopGasSteps input).cost = 701 := by
  unfold vLoopGasSteps
  simp only [Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [vExit_cost input]
  have hloop := Challenge.EvmProof.GasSteps.iterateBounded_cost_potential_eq
    8 81 (fun i => MachineState.memCost (24 + i))
    (fun i hi => vIterationGasSteps input i hi)
    (fun i hi => vIterationGasSteps_cost_potential input i hi)
  norm_num [MachineState.memCost] at hloop ⊢
  omega

def constantsGasSteps (input : ByteArray) :
    Challenge.EvmProof.GasSteps (constantsEntryState input)
      (constantsFinalState input) := by
  exact gasStepsBlock constantsPath (run_constants input) rfl rfl rfl
    deployAddress_not_precompile

theorem constants_path_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost constantsPath
      (constantsEntryState input) = 244 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    constantsPath 162 (run_constants input) rfl
    (by
      intro located hlocated
      have hall : constantsPath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  norm_num [constantsEntryState, constantsFinalState, MachineState.memCost,
    Challenge.EvmProof.Word.word_toNat_ofNat] at hpotential ⊢
  omega

@[simp] theorem constantsGasSteps_cost (input : ByteArray) :
    (constantsGasSteps input).cost = 244 := by
  exact constants_path_cost input

end Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization
