import Challenge.Modexp.Reference.Proofs.Bytecode.WordLoops
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# One-word MODEXP exit

The completed exponent residue is left-padded into one EVM word, stored at
memory `0x1800`, and returned with the declared modulus width.  This module
certifies that final control-flow and memory transition.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.WordExit

open EvmSemantics
open EvmSemantics.EVM
open Word
open WordLoops

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

private theorem wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def expFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 536 .JUMPDEST, opAt 537 .POP, opAt 538 (.Dup ⟨0, by decide⟩),
   opAt 539 (.Dup ⟨6, by decide⟩), pushAt 540 1 32, opAt 541 .SUB,
   pushAt 542 1 3, opAt 543 .SHL, opAt 544 .SHL,
   pushAt 545 2 6144, opAt 546 .MSTORE,
   opAt 547 (.Dup ⟨5, by decide⟩), pushAt 548 2 6144, opAt 549 .RETURN]

def expFinishDispatchState (input : ByteArray) (acc base : UInt256) : State :=
  { expLoopState input (exponentSize input) acc base with pc := UInt256.ofNat 669 }

def outputShift (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft
    ((32 : UInt256) - UInt256.ofNat (modulusSize input)) (UInt256.ofNat 3)

def outputWord (input : ByteArray) (acc : UInt256) : UInt256 :=
  UInt256.shiftLeft acc (outputShift input)

def outputMemory (input : ByteArray) (acc : UInt256) : ByteArray :=
  MachineState.writeBytes ByteArray.empty
    (Data.Bytes.natToBytesPadded (outputWord input acc).toNat 32) 6144

def wordFinalState (input : ByteArray) (acc base : UInt256) : State :=
  let start := expLoopState input (exponentSize input) acc base
  let storedWords := start.activeWordsAfterUInt256 6144 32
  { start with
    pc := UInt256.ofNat 688
    stack := [acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input
    memory := outputMemory input acc
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter storedWords.toNat
      6144 (modulusSize input))
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory input acc) 6144
      (modulusSize input) }

@[simp] private theorem exitPCs (i : Nat) (hi : 536 ≤ i) (hii : i ≤ 549) :
    Artifact.referenceArtifact.instructionPC i =
      [669,670,671,672,673,675,676,678,679,680,683,684,685,688][i - 536]! := by
  interval_cases i <;> decide

@[simp] private theorem jump669 :
    Decode.isValidJumpDest referenceBytecode 669 = true :=
  Artifact.isValidJumpDest_index 536 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_expFinishGuard (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expGuardPath
      (expLoopState input (exponentSize input) acc base) =
        some (expFinishDispatchState input acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have he256 : exponentSize input < 2 ^ 256 := by omega
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he256
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h669 : (669 : UInt256).toNat = 669 := by decide
  have h669Word : (669 : UInt256) = UInt256.ofNat 669 := by decide
  simp (config := { maxSteps := 150000 })
    [expGuardPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expLoopState, expFinishDispatchState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      he256, hemod, hzeroFalse, h669, h669Word, jump669]

set_option linter.unusedSimpArgs false in
theorem run_expFinishTail (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock expFinishTailPath
      (expFinishDispatchState input acc base) =
        some (wordFinalState input acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have h6144 : (6144 : UInt256).toNat = 6144 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have h3Word : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have hm256 : modulusSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm256
  have hmmodLiteral : modulusSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        modulusSize input := by
    norm_num at hmmod ⊢
    exact hmmod
  simp (config := { maxSteps := 350000 })
    [expFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expFinishDispatchState, expLoopState, wordFinalState, outputMemory,
      outputWord, outputShift, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, exitPCs,
      List.exchange, hsub, hshift, h6144, h32, h3Word, hm256, hmmod,
      hmmodLiteral, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

def gasSteps_expFinish (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps
      (expLoopState input (exponentSize input) acc base)
      (wordFinalState input acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka expGuardPath rfl rfl
        (run_expFinishGuard input acc base hvalid) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka expFinishTailPath rfl rfl
        (run_expFinishTail input acc base hvalid hword) rfl
        deployAddress_not_precompile)

@[simp] theorem wordFinalState_isDone (input : ByteArray) (acc base : UInt256) :
    (wordFinalState input acc base).isDone = true := by
  rfl

end Challenge.Modexp.Reference.Proofs.Bytecode.WordExit
