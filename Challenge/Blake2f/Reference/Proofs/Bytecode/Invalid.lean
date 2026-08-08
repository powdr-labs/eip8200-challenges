import Challenge.Blake2f.Reference.Proofs.Bytecode.Artifact
import Challenge.Blake2f.Reference.Proofs.Bytecode.GasCost
import Challenge.Blake2f.ProofSupport.InitialState
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Meter
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Direct execution certificates for the two malformed-input exits. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.Invalid

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def invalidLengthPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 46), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨37, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨38, .push ⟨2, by decide⟩ (UInt256.ofNat 91), by rfl, by decide⟩,
   ⟨39, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨72, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨73, .push ⟨2, by decide⟩ (UInt256.ofNat 337), by rfl, by decide⟩,
   ⟨74, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨232, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨233, .push ⟨1, by decide⟩ (UInt256.ofNat 213), by rfl, by decide⟩,
   ⟨234, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨235, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨236, .push ⟨2, by decide⟩ (UInt256.ofNat 347), by rfl, by decide⟩,
   ⟨237, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨238, .op .INVALID, by rfl, wfOp (by decide) trivial rfl⟩]

def invalidFlagPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 46), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨37, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨38, .push ⟨2, by decide⟩ (UInt256.ofNat 91), by rfl, by decide⟩,
   ⟨39, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨72, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨73, .push ⟨2, by decide⟩ (UInt256.ofNat 337), by rfl, by decide⟩,
   ⟨74, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨232, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨233, .push ⟨1, by decide⟩ (UInt256.ofNat 213), by rfl, by decide⟩,
   ⟨234, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨235, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨236, .push ⟨2, by decide⟩ (UInt256.ofNat 347), by rfl, by decide⟩,
   ⟨237, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨239, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨240, .push ⟨1, by decide⟩ (UInt256.ofNat 212), by rfl, by decide⟩,
   ⟨241, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨242, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨243, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨244, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨245, .op (.Dup ⟨1⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨246, .op .GT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨247, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨248, .push ⟨2, by decide⟩ (UInt256.ofNat 363), by rfl, by decide⟩,
   ⟨249, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨250, .op .INVALID, by rfl, wfOp (by decide) trivial rfl⟩]

def invalidLengthFinal (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 346
    halt := .Exception .InvalidInstruction }

def invalidFlagFinal (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 362
    stack := [UInt256.ofNat input[212]!.toNat]
    halt := .Exception .InvalidInstruction }

set_option linter.unusedSimpArgs false in
theorem run_invalidLength (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 213) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      invalidLengthPath (initialState referenceBytecode input 0) =
        some (invalidLengthFinal input) := by
  have h46 := Artifact.referenceArtifact.isValidJumpDest_index 37 (by rfl)
  have h91 := Artifact.referenceArtifact.isValidJumpDest_index 72 (by rfl)
  have h337 := Artifact.referenceArtifact.isValidJumpDest_index 232 (by rfl)
  have h46' : Decode.isValidJumpDest referenceBytecode 46 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h46
  have h91' : Decode.isValidJumpDest referenceBytecode 91 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h91
  have h337' : Decode.isValidJumpDest referenceBytecode 337 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h337
  have hsmall : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsmall' : input.size < UInt256.size := by exact hsmall
  norm_num [UInt256.size] at hsmall'
  have hzero : (0 : UInt256).toNat = 0 := by
    change (Fin.ofNat (2 ^ 256) 0).val = 0
    norm_num
  have hpc3 : (0 : UInt256) + UInt256.ofNat 3 = UInt256.ofNat 3 := by
    change UInt256.ofNat 0 + UInt256.ofNat 3 = UInt256.ofNat 3
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 0) (b := 3) (by norm_num)
  have hpc50 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 47) (b := 3) (by norm_num)
  have hpc95 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 92) (b := 3) (by norm_num)
  have hpc340 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 338) (b := 2) (by norm_num)
  have hpc345 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 342) (b := 3) (by norm_num)
  simp [Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Challenge.EvmProof.Stepper.WellFormed,
    invalidLengthPath, invalidLengthFinal, Artifact.referenceArtifact,
    Artifact.referenceInstructions, Challenge.EvmProof.ProgramArtifact.instructionPC,
    initialState, hsize,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat,
    UInt256.eq, UInt256.isTrue, Gas.baseCost,
    hzero, hpc3, hpc50, hpc95, hpc340, hpc345,
    h46', h91', h337']
  rw [Nat.mod_eq_of_lt hsmall']
  simp [hsize, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_invalidFlag (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : 1 < input[212]!.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock
      invalidFlagPath (initialState referenceBytecode input 0) =
        some (invalidFlagFinal input) := by
  have h46 := Artifact.referenceArtifact.isValidJumpDest_index 37 (by rfl)
  have h91 := Artifact.referenceArtifact.isValidJumpDest_index 72 (by rfl)
  have h337 := Artifact.referenceArtifact.isValidJumpDest_index 232 (by rfl)
  have h347 := Artifact.referenceArtifact.isValidJumpDest_index 239 (by rfl)
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
  have hsmall : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsmall' : input.size < UInt256.size := by exact hsmall
  norm_num [UInt256.size] at hsmall'
  have hzero : (0 : UInt256).toNat = 0 := by
    change (Fin.ofNat (2 ^ 256) 0).val = 0
    norm_num
  have hbyteFrom : YulSemantics.EVM.byteFrom input.toList 212 = input[212]! := by
    have h := Challenge.EvmProof.Bytes.memMatch_toList input 212
    have hi : 212 < input.size := by omega
    simp [hi] at h
    rw [getElem!_pos input 212 hi]
    exact h
  have hbyte : UInt256.byteAt ⟨0⟩ (MachineState.readWord input 212) =
      UInt256.ofNat input[212]!.toNat := by
    rw [Challenge.EvmProof.Bytes.byteAt_zero_readWord, hbyteFrom]
  have hflag' : 1 < input[212].toNat := by
    simpa [getElem!_pos input 212 (by omega)] using hflag
  have hflagMod : 1 < input[212].toNat % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (Nat.lt_trans input[212].toNat_lt (by norm_num))]
    exact hflag'
  norm_num at hflagMod
  have hone : (UInt256.ofNat 1).toNat = 1 := by
    norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hpc3 : (0 : UInt256) + UInt256.ofNat 3 = UInt256.ofNat 3 := by
    change UInt256.ofNat 0 + UInt256.ofNat 3 = UInt256.ofNat 3
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 0) (b := 3) (by norm_num)
  have hpc50 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 47) (b := 3) (by norm_num)
  have hpc95 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 92) (b := 3) (by norm_num)
  have hpc340 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 338) (b := 2) (by norm_num)
  have hpc345 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 342) (b := 3) (by norm_num)
  have hpc350 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 348) (b := 2) (by norm_num)
  have hpc355 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 353) (b := 2) (by norm_num)
  have hpc361 := Challenge.EvmProof.Word.ofNat_add_ofNat (a := 358) (b := 3) (by norm_num)
  simp [Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Challenge.EvmProof.Stepper.WellFormed,
    invalidFlagPath, invalidFlagFinal, Artifact.referenceArtifact,
    Artifact.referenceInstructions, Challenge.EvmProof.ProgramArtifact.instructionPC,
    initialState, hsize, hflag, hflag', hflagMod, hbyte, hone,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat,
    UInt256.eq, UInt256.gt, UInt256.isTrue, UInt256.isZero, Gas.baseCost,
    hzero, hpc3, hpc50, hpc95, hpc340, hpc345, hpc350, hpc355, hpc361,
    h46', h91', h337', h347']

def gasSteps_invalidLength (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 213) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (invalidLengthFinal input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact
    .Osaka invalidLengthPath
  · rfl
  · rfl
  · exact run_invalidLength input hfit hsize
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_invalidFlag (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : 1 < input[212]!.toNat) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (invalidFlagFinal input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact
    .Osaka invalidFlagPath
  · rfl
  · rfl
  · exact run_invalidFlag input hfit hsize hflag
  · rfl
  · exact deployAddress_not_precompile

theorem invalidLengthPath_cost (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 213) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost invalidLengthPath
        (initialState referenceBytecode input 0) = GasCost.invalidLengthCost := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    invalidLengthPath GasCost.invalidLengthCost (run_invalidLength input hfit hsize) rfl
    (by
      intro located hlocated
      have hall : invalidLengthPath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  simpa [initialState, invalidLengthFinal, GasCost.invalidLengthCost,
    MachineState.memCost] using hpotential

theorem invalidFlagPath_cost (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 213) (hflag : 1 < input[212]!.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost invalidFlagPath
        (initialState referenceBytecode input 0) = GasCost.invalidFlagCost := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    invalidFlagPath GasCost.invalidFlagCost (run_invalidFlag input hfit hsize hflag) rfl
    (by
      intro located hlocated
      have hall : invalidFlagPath.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  simpa [initialState, invalidFlagFinal, GasCost.invalidFlagCost,
    MachineState.memCost] using hpotential

@[simp] theorem gasSteps_invalidLength_cost (input : ByteArray)
    (hfit : CalldataFits input) (hsize : input.size ≠ 213) :
    (gasSteps_invalidLength input hfit hsize).cost = GasCost.invalidLengthCost := by
  exact invalidLengthPath_cost input hfit hsize

@[simp] theorem gasSteps_invalidFlag_cost (input : ByteArray)
    (hfit : CalldataFits input) (hsize : input.size = 213)
    (hflag : 1 < input[212]!.toNat) :
    (gasSteps_invalidFlag input hfit hsize hflag).cost = GasCost.invalidFlagCost := by
  exact invalidFlagPath_cost input hfit hsize hflag

end Challenge.Blake2f.Reference.Proofs.Bytecode.Invalid
