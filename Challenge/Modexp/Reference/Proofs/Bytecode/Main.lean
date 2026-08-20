import Challenge.Modexp.ProofSupport
import Challenge.Modexp.Reference.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# MODEXP bytecode entry and header validation

This is the first execution certificate for the frozen artifact.  It follows
the compiler's function-declaration trampolines, reads the three EIP-198
header words, proves the EIP-7823 checks take their successful edge, and
stops at the operand dispatcher.  The same `GasSteps` witness is used by the
functional proof and by the exact gas schedule.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

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

/-- First half of the compiler trampoline chain. -/
def trampoline1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 0 2 14, opAt 1 .JUMP,
   opAt 12 .JUMPDEST, pushAt 13 2 53, opAt 14 .JUMP,
   opAt 43 .JUMPDEST, pushAt 44 2 99, opAt 45 .JUMP,
   opAt 80 .JUMPDEST, pushAt 81 2 305, opAt 82 .JUMP]

/-- Second half of the compiler trampoline chain. -/
def trampoline2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 262 .JUMPDEST, pushAt 263 2 434, opAt 264 .JUMP,
   opAt 350 .JUMPDEST, pushAt 351 2 512, opAt 352 .JUMP,
   opAt 412 .JUMPDEST, pushAt 413 2 699, opAt 414 .JUMP,
   opAt 560 .JUMPDEST, pushAt 561 2 1196, opAt 562 .JUMP,
   opAt 899 .JUMPDEST]

/-- Three EIP-198 header loads. -/
def headerLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 900 0 0, opAt 901 .CALLDATALOAD,
   pushAt 902 1 32, opAt 903 .CALLDATALOAD,
   pushAt 904 1 64, opAt 905 .CALLDATALOAD]

/-- Successful EIP-7823 bound check. -/
def headerCheckPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 906 2 1024, opAt 907 (.Dup ⟨1, by decide⟩), opAt 908 .GT,
   pushAt 909 2 1024, opAt 910 (.Dup ⟨3, by decide⟩), opAt 911 .GT,
   pushAt 912 2 1024, opAt 913 (.Dup ⟨5, by decide⟩), opAt 914 .GT,
   opAt 915 .OR, opAt 916 .OR, opAt 917 .ISZERO,
   pushAt 918 2 1228, opAt 919 .JUMPI]

/-- Reachable instructions from byte zero through the successful header
check, retained as a single audit-friendly path. -/
def headerPath := trampoline1Path ++ trampoline2Path ++
  headerLoadPath ++ headerCheckPath

def tramp0Path := [pushAt 0 2 14, opAt 1 .JUMP]
def tramp1Path := [opAt 12 .JUMPDEST, pushAt 13 2 53, opAt 14 .JUMP]
def tramp2Path := [opAt 43 .JUMPDEST, pushAt 44 2 99, opAt 45 .JUMP]
def tramp3Path := [opAt 80 .JUMPDEST, pushAt 81 2 305, opAt 82 .JUMP]
def tramp4Path := [opAt 262 .JUMPDEST, pushAt 263 2 434, opAt 264 .JUMP]
def tramp5Path := [opAt 350 .JUMPDEST, pushAt 351 2 512, opAt 352 .JUMP]
def tramp6Path := [opAt 412 .JUMPDEST, pushAt 413 2 699, opAt 414 .JUMP]
def tramp7Path := [opAt 560 .JUMPDEST, pushAt 561 2 1196, opAt 562 .JUMP,
  opAt 899 .JUMPDEST]
def tramp7JumpPath := [opAt 560 .JUMPDEST, pushAt 561 2 1196, opAt 562 .JUMP]
def tramp7DestPath := [opAt 899 .JUMPDEST]

def trampolineState (input : ByteArray) (pc : Nat) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat pc }

/-- Gas-erased state at the midpoint of the trampoline chain. -/
def trampolineMidState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat 305 }

/-- Gas-erased state at the public entry point. -/
def headerEntryState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat 1197 }

/-- Gas-erased state after loading the three header words. -/
def headerLoadedState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 1205
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Gas-erased state immediately after the successful size-check jump. -/
def headerState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 1228
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

private theorem headerWord (input : ByteArray) (offset : Nat) :
    MachineState.readWord input offset =
      UInt256.ofNat (Precompile.bytesToNatPadded input offset 32) := rfl

private theorem size_lt_word {n : Nat} (h : n ≤ 1024) : n < 2 ^ 256 := by
  omega

@[simp] private theorem headerPCs0 (i : Nat) (hi : i ≤ 1) :
    Artifact.referenceArtifact.instructionPC i = [0, 3][i]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs12 (i : Nat) (hi : 12 ≤ i) (hii : i ≤ 14) :
    Artifact.referenceArtifact.instructionPC i = [14, 15, 18][i - 12]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs43 (i : Nat) (hi : 43 ≤ i) (hii : i ≤ 45) :
    Artifact.referenceArtifact.instructionPC i = [53, 54, 57][i - 43]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs80 (i : Nat) (hi : 80 ≤ i) (hii : i ≤ 82) :
    Artifact.referenceArtifact.instructionPC i = [99, 100, 103][i - 80]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs262 (i : Nat) (hi : 262 ≤ i) (hii : i ≤ 264) :
    Artifact.referenceArtifact.instructionPC i = [305, 306, 309][i - 262]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs350 (i : Nat) (hi : 350 ≤ i) (hii : i ≤ 352) :
    Artifact.referenceArtifact.instructionPC i = [434, 435, 438][i - 350]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs412 (i : Nat) (hi : 412 ≤ i) (hii : i ≤ 414) :
    Artifact.referenceArtifact.instructionPC i = [512, 513, 516][i - 412]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs560 (i : Nat) (hi : 560 ≤ i) (hii : i ≤ 562) :
    Artifact.referenceArtifact.instructionPC i = [699, 700, 703][i - 560]! := by
  interval_cases i <;> decide

@[simp] private theorem headerPCs899 (i : Nat) (hi : 899 ≤ i) (hii : i ≤ 919) :
    Artifact.referenceArtifact.instructionPC i =
      [1196,1197,1198,1199,1201,1202,1204,1205,1208,1209,1210,
       1213,1214,1215,1218,1219,1220,1221,1222,1223,1226][i - 899]! := by
  interval_cases i <;> decide

@[simp] private theorem jump14 :
    Decode.isValidJumpDest referenceBytecode 14 = true :=
  Artifact.isValidJumpDest_index 12 (by rfl)

@[simp] private theorem jump53 :
    Decode.isValidJumpDest referenceBytecode 53 = true :=
  Artifact.isValidJumpDest_index 43 (by rfl)

@[simp] private theorem jump99 :
    Decode.isValidJumpDest referenceBytecode 99 = true :=
  Artifact.isValidJumpDest_index 80 (by rfl)

@[simp] private theorem jump305 :
    Decode.isValidJumpDest referenceBytecode 305 = true :=
  Artifact.isValidJumpDest_index 262 (by rfl)

@[simp] private theorem jump434 :
    Decode.isValidJumpDest referenceBytecode 434 = true :=
  Artifact.isValidJumpDest_index 350 (by rfl)

@[simp] private theorem jump512 :
    Decode.isValidJumpDest referenceBytecode 512 = true :=
  Artifact.isValidJumpDest_index 412 (by rfl)

@[simp] private theorem jump699 :
    Decode.isValidJumpDest referenceBytecode 699 = true :=
  Artifact.isValidJumpDest_index 560 (by rfl)

@[simp] private theorem jump1196 :
    Decode.isValidJumpDest referenceBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

@[simp] private theorem jump1228 :
    Decode.isValidJumpDest referenceBytecode 1228 = true :=
  Artifact.isValidJumpDest_index 921 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState referenceBytecode input 0) = some (trampolineState input 14) := by
  have hzero : (0 : UInt256).toNat = 0 := by decide
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 0) (b := 3) (by norm_num : 0 + 3 < 2 ^ 256)
  have hdest : (14 : UInt256).toNat = 14 := by decide
  simp [tramp0Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hzero, hadd, hdest]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp1Path
      (trampolineState input 14) = some (trampolineState input 53) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 14) (by norm_num : 14 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 15) (b := 3) (by norm_num : 15 + 3 < 2 ^ 256)
  have hdest : (53 : UInt256).toNat = 53 := by decide
  simp [tramp1Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp2 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp2Path
      (trampolineState input 53) = some (trampolineState input 99) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 53) (by norm_num : 53 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 54) (b := 3) (by norm_num : 54 + 3 < 2 ^ 256)
  have hdest : (99 : UInt256).toNat = 99 := by decide
  simp [tramp2Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp3 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp3Path
      (trampolineState input 99) = some (trampolineState input 305) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 99) (by norm_num : 99 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 100) (b := 3) (by norm_num : 100 + 3 < 2 ^ 256)
  have hdest : (305 : UInt256).toNat = 305 := by decide
  simp [tramp3Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp4 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp4Path
      (trampolineState input 305) = some (trampolineState input 434) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 305) (by norm_num : 305 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 306) (b := 3) (by norm_num : 306 + 3 < 2 ^ 256)
  have hdest : (434 : UInt256).toNat = 434 := by decide
  simp [tramp4Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp5 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp5Path
      (trampolineState input 434) = some (trampolineState input 512) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 434) (by norm_num : 434 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 435) (b := 3) (by norm_num : 435 + 3 < 2 ^ 256)
  have hdest : (512 : UInt256).toNat = 512 := by decide
  simp [tramp5Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp6 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp6Path
      (trampolineState input 512) = some (trampolineState input 699) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 512) (by norm_num : 512 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 513) (b := 3) (by norm_num : 513 + 3 < 2 ^ 256)
  have hdest : (699 : UInt256).toNat = 699 := by decide
  simp [tramp6Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp7 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7Path
      (trampolineState input 699) = some (headerEntryState input) := by
  have hsucc699 := Challenge.EvmProof.Word.succ_ofNat
    (n := 699) (by norm_num : 699 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 700) (b := 3) (by norm_num : 700 + 3 < 2 ^ 256)
  have hdest : (1196 : UInt256).toNat = 1196 := by decide
  have hsucc1196 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1196) (by norm_num : 1196 + 1 < 2 ^ 256)
  simp [tramp7Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, headerEntryState, initialState,
    hsucc699, hadd, hdest, hsucc1196,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp7Jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7JumpPath
      (trampolineState input 699) = some (trampolineState input 1196) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 699) (by norm_num : 699 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 700) (b := 3) (by norm_num : 700 + 3 < 2 ^ 256)
  have hdest : (1196 : UInt256).toNat = 1196 := by decide
  simp [tramp7JumpPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7DestPath
      (trampolineState input 1196) = some (headerEntryState input) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 1196) (by norm_num : 1196 + 1 < 2 ^ 256)
  simp [tramp7DestPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, headerEntryState, initialState, hsucc,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_headerLoad (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerLoadPath
      (headerEntryState input) = some (headerLoadedState input) := by
  have hs1197 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1197) (by norm_num : 1197 + 1 < 2 ^ 256)
  have hs1198 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1198) (by norm_num : 1198 + 1 < 2 ^ 256)
  have ha1199 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1199) (b := 2) (by norm_num : 1199 + 2 < 2 ^ 256)
  have hs1201 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1201) (by norm_num : 1201 + 1 < 2 ^ 256)
  have ha1202 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1202) (b := 2) (by norm_num : 1202 + 2 < 2 ^ 256)
  have hs1204 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1204) (by norm_num : 1204 + 1 < 2 ^ 256)
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have h64 : (64 : UInt256).toNat = 64 := by decide
  simp (config := { maxSteps := 200000 })
    [headerLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      headerEntryState, headerLoadedState, initialState, headerWord,
      baseSize, exponentSize, modulusSize,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hs1197, hs1198, ha1199, hs1201, ha1202, hs1204, h0, h32, h64]; rfl

set_option linter.unusedSimpArgs false in
theorem run_headerCheck (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerCheckPath
      (headerLoadedState input) = some (headerState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb' := size_lt_word hb
  have he' := size_lt_word he
  have hm' := size_lt_word hm
  have hbmod : baseSize input % 2 ^ 256 = baseSize input := Nat.mod_eq_of_lt hb'
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input := Nat.mod_eq_of_lt he'
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input := Nat.mod_eq_of_lt hm'
  have hbraw : Precompile.bytesToNatPadded input 0 32 ≤ 1024 := by
    simpa [baseSize] using hb
  have heraw : Precompile.bytesToNatPadded input 32 32 ≤ 1024 := by
    simpa [exponentSize] using he
  have hmraw : Precompile.bytesToNatPadded input 64 32 ≤ 1024 := by
    simpa [modulusSize] using hm
  have hbrawmod : Precompile.bytesToNatPadded input 0 32 % 2 ^ 256 =
      Precompile.bytesToNatPadded input 0 32 := by
    exact Nat.mod_eq_of_lt (by omega)
  have herawmod : Precompile.bytesToNatPadded input 32 32 % 2 ^ 256 =
      Precompile.bytesToNatPadded input 32 32 := by
    exact Nat.mod_eq_of_lt (by omega)
  have hmrawmod : Precompile.bytesToNatPadded input 64 32 % 2 ^ 256 =
      Precompile.bytesToNatPadded input 64 32 := by
    exact Nat.mod_eq_of_lt (by omega)
  have h1024 : (1024 : UInt256).toNat = 1024 := by decide
  have hgtb : UInt256.gt
      (UInt256.ofNat (Precompile.bytesToNatPadded input 0 32)) 1024 = 0 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h1024]
    rw [if_neg]
    · rfl
    · have hmod := Nat.mod_le (Precompile.bytesToNatPadded input 0 32) (2 ^ 256)
      omega
  have hgte : UInt256.gt
      (UInt256.ofNat (Precompile.bytesToNatPadded input 32 32)) 1024 = 0 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h1024]
    rw [if_neg]
    · rfl
    · have hmod := Nat.mod_le (Precompile.bytesToNatPadded input 32 32) (2 ^ 256)
      omega
  have hgtm : UInt256.gt
      (UInt256.ofNat (Precompile.bytesToNatPadded input 64 32)) 1024 = 0 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h1024]
    rw [if_neg]
    · rfl
    · have hmod := Nat.mod_le (Precompile.bytesToNatPadded input 64 32) (2 ^ 256)
      omega
  have hlor : UInt256.lor (UInt256.lor 0 0) 0 = 0 := by decide
  have hiz : UInt256.isZero 0 = 1 := by decide
  have htrue : UInt256.isTrue 1 := by decide
  have h1 : (1 : UInt256).toNat = 1 := by decide
  have ha1205 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1205) (b := 3) (by norm_num : 1205 + 3 < 2 ^ 256)
  have hs1208 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1208) (by norm_num : 1208 + 1 < 2 ^ 256)
  have hs1209 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1209) (by norm_num : 1209 + 1 < 2 ^ 256)
  have ha1210 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1210) (b := 3) (by norm_num : 1210 + 3 < 2 ^ 256)
  have hs1213 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1213) (by norm_num : 1213 + 1 < 2 ^ 256)
  have hs1214 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1214) (by norm_num : 1214 + 1 < 2 ^ 256)
  have ha1215 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1215) (b := 3) (by norm_num : 1215 + 3 < 2 ^ 256)
  have hs1218 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1218) (by norm_num : 1218 + 1 < 2 ^ 256)
  have hs1219 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1219) (by norm_num : 1219 + 1 < 2 ^ 256)
  have hs1220 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1220) (by norm_num : 1220 + 1 < 2 ^ 256)
  have hs1221 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1221) (by norm_num : 1221 + 1 < 2 ^ 256)
  have hs1222 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1222) (by norm_num : 1222 + 1 < 2 ^ 256)
  have ha1223 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1223) (b := 3) (by norm_num : 1223 + 3 < 2 ^ 256)
  have hdest : (1228 : UInt256).toNat = 1228 := by decide
  simp (config := { maxSteps := 200000 })
    [headerCheckPath, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerLoadedState, headerState, initialState,
    baseSize, exponentSize, modulusSize,
    UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hb, he, hm, hb', he', hm', hbmod, hemod, hmmod,
    hbraw, heraw, hmraw, hbrawmod, herawmod, hmrawmod, h1024,
    hgtb, hgte, hgtm, hlor, hiz, htrue, h1,
    ha1205, hs1208, hs1209, ha1210,
    hs1213, hs1214, ha1215, hs1218, hs1219, hs1220, hs1221,
    hs1222, ha1223, hdest]; rfl

private def gasSteps_tramp0 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (trampolineState input 14) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp0Path rfl rfl (run_tramp0 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 14)
      (trampolineState input 53) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp1Path rfl rfl (run_tramp1 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 53)
      (trampolineState input 99) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp2Path rfl rfl (run_tramp2 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp3 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 99)
      (trampolineState input 305) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp3Path rfl rfl (run_tramp3 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp4 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 305)
      (trampolineState input 434) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp4Path rfl rfl (run_tramp4 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp5 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 434)
      (trampolineState input 512) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp5Path rfl rfl (run_tramp5 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp6 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 512)
      (trampolineState input 699) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp6Path rfl rfl (run_tramp6 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp7 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 699)
      (headerEntryState input) := by
  apply Challenge.EvmProof.GasSteps.trans
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka tramp7JumpPath rfl rfl
        (run_tramp7Jump input) rfl deployAddress_not_precompile
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka tramp7DestPath rfl rfl
        (run_tramp7Dest input) rfl deployAddress_not_precompile

private def gasSteps_headerLoad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (headerEntryState input)
      (headerLoadedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka headerLoadPath rfl rfl (run_headerLoad input)
      rfl deployAddress_not_precompile

private def gasSteps_headerCheck (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (headerLoadedState input) (headerState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka headerCheckPath rfl rfl
      (run_headerCheck input hvalid) rfl deployAddress_not_precompile

@[simp] private theorem gasSteps_tramp0_cost (input : ByteArray) :
    (gasSteps_tramp0 input).cost = 11 := by rfl

@[simp] private theorem gasSteps_tramp1_cost (input : ByteArray) :
    (gasSteps_tramp1 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp2_cost (input : ByteArray) :
    (gasSteps_tramp2 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp3_cost (input : ByteArray) :
    (gasSteps_tramp3 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp4_cost (input : ByteArray) :
    (gasSteps_tramp4 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp5_cost (input : ByteArray) :
    (gasSteps_tramp5 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp6_cost (input : ByteArray) :
    (gasSteps_tramp6 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp7_cost (input : ByteArray) :
    (gasSteps_tramp7 input).cost = 13 := by rfl

@[simp] private theorem gasSteps_headerLoad_cost (input : ByteArray) :
    (gasSteps_headerLoad input).cost = 17 := by rfl

@[simp] private theorem gasSteps_headerCheck_cost
    (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_headerCheck input hvalid).cost = 49 := by rfl

/-- Header parsing as a gas-parametric relational trace. -/
def gasSteps_header (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (headerState input) := by
  exact (gasSteps_tramp0 input).trans <|
    (gasSteps_tramp1 input).trans <|
    (gasSteps_tramp2 input).trans <|
    (gasSteps_tramp3 input).trans <|
    (gasSteps_tramp4 input).trans <|
    (gasSteps_tramp5 input).trans <|
    (gasSteps_tramp6 input).trans <|
    (gasSteps_tramp7 input).trans <|
    (gasSteps_headerLoad input).trans (gasSteps_headerCheck input hvalid)

/-- Exact, input-independent gas used by the compiler trampolines and the
three successful EIP-7823 size checks. -/
theorem gasSteps_header_cost (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_header input hvalid).cost = 162 := by
  simp [gasSteps_header]

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
