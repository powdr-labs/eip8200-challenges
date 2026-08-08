import Challenge.Blake2f.Reference.Proofs.Bytecode.Artifact
import Challenge.Blake2f.ProofSupport.InitialState
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Valid-input entry trace

This module certifies validation and decoding of the two scalar inputs retained
on the reference program's stack: the final flag and the 32-bit round count.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.Prelude

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def validPreludePath := Artifact.locatedPath
  [0, 1, 37, 38, 39, 72, 73, 74,
   232, 233, 234, 235, 236, 237,
   239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
   251, 252, 253, 254, 255, 256, 257]

def finalFlagWord (input : ByteArray) : UInt256 :=
  UInt256.ofNat input[212]!.toNat

def roundsWord (input : ByteArray) : UInt256 := UInt256.ofNat (rounds input)

def finalState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 371
    stack := [⟨0⟩, roundsWord input, finalFlagWord input] }

private theorem readPadded_four (input : ByteArray) (hsize : 4 ≤ input.size) :
    MachineState.readPadded input 0 4 = input.extract 0 4 := by
  unfold MachineState.readPadded
  simp only [Nat.min_eq_left (Nat.zero_le _), Nat.sub_zero]
  simp only [Nat.min_eq_right hsize, Nat.zero_add, Nat.sub_self,
    Array.replicate_zero]
  exact ByteArray.append_empty

theorem shiftRight_rounds (input : ByteArray) (hsize : 4 ≤ input.size) :
    UInt256.shiftRight (MachineState.readWord input 0) (UInt256.ofNat 224) =
      roundsWord input := by
  rw [Challenge.EvmProof.Bytes.shiftRight_readWord input 0 4 (by omega) (by omega)]
  change UInt256.ofNat (Precompile.bytesToNatPadded input 0 4) =
    UInt256.ofNat (Data.Bytes.bytesToBigEndianNat (input.extract 0 4))
  unfold Precompile.bytesToNatPadded
  rw [readPadded_four input hsize]

theorem run (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : input[212]!.toNat ≤ 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock validPreludePath
        (initialState referenceBytecode input 0) = some (finalState input) := by
  have h46 := Artifact.referenceArtifact.isValidJumpDest_index 37 (by rfl)
  have h91 := Artifact.referenceArtifact.isValidJumpDest_index 72 (by rfl)
  have h337 := Artifact.referenceArtifact.isValidJumpDest_index 232 (by rfl)
  have h347 := Artifact.referenceArtifact.isValidJumpDest_index 239 (by rfl)
  have h363 := Artifact.referenceArtifact.isValidJumpDest_index 251 (by rfl)
  have h46' : Decode.isValidJumpDest referenceBytecode 46 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h46
  have h91' : Decode.isValidJumpDest referenceBytecode 91 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h91
  have h337' : Decode.isValidJumpDest referenceBytecode 337 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h337
  have h347' : Decode.isValidJumpDest referenceBytecode 347 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h347
  have h363' : Decode.isValidJumpDest referenceBytecode 363 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h363
  have hsmall : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsmall' : input.size < UInt256.size := by exact hsmall
  norm_num [UInt256.size] at hsmall'
  have hzero : (0 : UInt256).toNat = 0 := by
    change (Fin.ofNat (2 ^ 256) 0).val = 0
    norm_num
  have hzeroStruct : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hone : (UInt256.ofNat 1).toNat = 1 := by
    norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hbyteFrom : YulSemantics.EVM.byteFrom input.toList 212 = input[212]! := by
    have h := Challenge.EvmProof.Bytes.memMatch_toList input 212
    have hi : 212 < input.size := by omega
    simp [hi] at h
    rw [getElem!_pos input 212 hi]
    exact h
  have hbyte : UInt256.byteAt ⟨0⟩ (MachineState.readWord input 212) =
      finalFlagWord input := by
    rw [Challenge.EvmProof.Bytes.byteAt_zero_readWord, hbyteFrom]
    rfl
  have hflagMod : input[212]!.toNat % 2 ^ 256 ≤ 1 := by
    rw [Nat.mod_eq_of_lt (Nat.lt_trans input[212]!.toNat_lt (by norm_num))]
    exact hflag
  norm_num at hflagMod
  have hflagElem : input[212].toNat ≤ 1 := by
    simpa [getElem!_pos input 212 (by omega)] using hflag
  have hflagElemMod :
      input[212].toNat %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        input[212].toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans input[212].toNat_lt (by norm_num))
  have hnotFlagElem : ¬1 < input[212].toNat := by omega
  have hpc3 : UInt256.ofNat 0 + UInt256.ofNat 3 = UInt256.ofNat 3 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 0) (b := 3) (by norm_num)
  have hpc50 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 47) (b := 3) (by norm_num)
  have hpc95 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 92) (b := 3) (by norm_num)
  have hpc340 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 338) (b := 2) (by norm_num)
  have hpc345 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 342) (b := 3) (by norm_num)
  have hpc350 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 348) (b := 2) (by norm_num)
  have hpc355 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 353) (b := 2) (by norm_num)
  have hpc361 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 358) (b := 3) (by norm_num)
  have hpc368 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 366) (b := 2) (by norm_num)
  simp (config := { maxSteps := 1000000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Challenge.EvmProof.Stepper.WellFormed,
    validPreludePath, Artifact.locatedPath, Artifact.located,
    Challenge.EvmProof.Stepper.Located.ofIndex,
    finalState, finalFlagWord, Artifact.referenceArtifact,
    Artifact.referenceInstructions, Challenge.EvmProof.ProgramArtifact.instructionPC,
    initialState, hsize, hflag, hflagMod, hflagElem, hflagElemMod,
    hnotFlagElem, hbyte,
    shiftRight_rounds input (by omega),
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat,
    UInt256.eq, UInt256.gt, UInt256.isTrue, UInt256.isZero, Gas.baseCost,
    hzero, hzeroStruct, hone, hpc3, hpc50, hpc95, hpc340, hpc345, hpc350, hpc355,
    hpc361, hpc368, h46', h91', h337', h347', h363']

def gasSteps (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : input[212]!.toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (finalState input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact
    .Osaka validPreludePath
  · rfl
  · rfl
  · exact run input hfit hsize hflag
  · rfl
  · exact deployAddress_not_precompile

theorem path_cost (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : input[212]!.toNat ≤ 1) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost validPreludePath
        (initialState referenceBytecode input 0) = 109 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    validPreludePath 109 (run input hfit hsize hflag) rfl
    (by
      intro located hlocated
      have hall : validPreludePath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  simpa [initialState, finalState, MachineState.memCost] using hpotential

@[simp] theorem gasSteps_cost (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : input[212]!.toNat ≤ 1) :
    (gasSteps input hfit hsize hflag).cost = 109 := by
  exact path_cost input hfit hsize hflag

end Challenge.Blake2f.Reference.Proofs.Bytecode.Prelude
