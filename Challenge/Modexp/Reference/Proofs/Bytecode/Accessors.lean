import Challenge.Modexp.Reference.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Meter
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Certified calldata-byte helper

The compiler lowers `calldataByte` to an internal jump.  This summary exposes
its ordinary input/output contract and its exact constant gas cost.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Accessors

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def calldataBytePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨2, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨5, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨6, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨7, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨8, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨9, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨10, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨11, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def calldataByteValue (s : State) (offset : UInt256) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord s.executionEnv.calldata offset.toNat)

def calldataByteEntry (s : State) (offset output returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4
    stack := [offset, output, returnDest] ++ rest }

def calldataByteReturned (s : State) (offset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := calldataByteValue s offset :: rest }

@[simp] private theorem helperPCs (i : Nat) (hi : 2 ≤ i) (hii : i ≤ 11) :
    Artifact.referenceArtifact.instructionPC i = i + 2 := by
  interval_cases i <;> decide

@[simp] private theorem helperNext (i : Nat) (hi : 4 ≤ i) (hii : i ≤ 13) :
    (UInt256.ofNat i).succ = UInt256.ofNat (i + 1) := by
  exact Challenge.EvmProof.Word.succ_ofNat (by omega)

set_option linter.unusedSimpArgs false in
theorem run_calldataByte (s : State) (offset output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock calldataBytePath
      (calldataByteEntry s offset output returnDest rest) =
        some (calldataByteReturned s offset returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp (config := { maxSteps := 150000 })
    [calldataBytePath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      calldataByteEntry, calldataByteReturned, calldataByteValue, List.exchange,
      hc1, hc2, hc3, hc4, hc5, hcode, hrun, hvalid, helperPCs, helperNext]

def gasSteps_calldataByte (s : State) (offset output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (calldataByteEntry s offset output returnDest rest)
      (calldataByteReturned s offset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka calldataBytePath
  · exact hcode
  · exact hfork
  · exact run_calldataByte s offset output returnDest rest hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

theorem gasSteps_calldataByte_cost_potential (s : State)
    (offset output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (gasSteps_calldataByte s offset output returnDest rest hcap hcode hfork
        hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      30 + MachineState.memCost
        (calldataByteReturned s offset returnDest rest).activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    calldataBytePath 30
      (run_calldataByte s offset output returnDest rest hcap hcode hrun hvalid)
      hfork (by decide) (by decide)
  unfold gasSteps_calldataByte
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [calldataByteEntry, calldataByteReturned] using hmeter

end Challenge.Modexp.Reference.Proofs.Bytecode.Accessors
