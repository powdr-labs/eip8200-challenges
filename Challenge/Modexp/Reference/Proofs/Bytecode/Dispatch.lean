import Challenge.Modexp.Reference.Proofs.Bytecode.Main
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# MODEXP output dispatcher

The zero-width EIP-198 result is a complete terminating bytecode path.  It is
kept separate because it touches no operand bytes or memory and therefore has
the challenge's minimum gas cost.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch

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

def zeroSizePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 921 .JUMPDEST, opAt 922 (.Dup ⟨0, by decide⟩),
   pushAt 923 2 1237, opAt 924 .JUMPI,
   pushAt 925 0 0, pushAt 926 0 0, opAt 927 .RETURN]

def wordEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 921 .JUMPDEST, opAt 922 (.Dup ⟨0, by decide⟩),
   pushAt 923 2 1237, opAt 924 .JUMPI,
   opAt 928 .JUMPDEST, opAt 929 (.Dup ⟨2, by decide⟩),
   pushAt 930 1 96, opAt 931 .ADD,
   opAt 932 (.Dup ⟨2, by decide⟩), opAt 933 (.Dup ⟨1, by decide⟩),
   opAt 934 .ADD, pushAt 935 1 32, opAt 936 (.Dup ⟨3, by decide⟩),
   opAt 937 .GT, pushAt 938 2 1268, opAt 939 .JUMPI,
   pushAt 940 2 1267, opAt 941 (.Dup ⟨1, by decide⟩),
   opAt 942 (.Dup ⟨3, by decide⟩), pushAt 943 1 96,
   opAt 944 (.Dup ⟨6, by decide⟩), opAt 945 (.Dup ⟨8, by decide⟩),
   opAt 946 (.Dup ⟨10, by decide⟩), pushAt 947 2 517, opAt 948 .JUMP]

def zeroSetupPath := zeroSizePath.take 6
def zeroReturnPath := [opAt 927 .RETURN]
def wordJumpPath := wordEntryPath.take 4
def wordRestPath := wordEntryPath.drop 4
def wordCheckPath := wordRestPath.take 12
def wordTailPath := wordRestPath.drop 12

@[simp] private theorem dispatchPCs (i : Nat) (hi : 921 ≤ i) (hii : i ≤ 948) :
    Artifact.referenceArtifact.instructionPC i =
      [1228,1229,1230,1233,1234,1235,1236,1237,1238,1239,1241,1242,
       1243,1244,1245,1247,1248,1249,1252,1253,1256,1257,1258,1260,
       1261,1262,1263,1266][i - 921]! := by
  interval_cases i <;> decide

@[simp] private theorem activeWordsAfterUInt256_zero (s : State) (offset : Nat) :
    s.activeWordsAfterUInt256 offset 0 = UInt256.ofNat s.activeWords.toNat := by
  simp [State.activeWordsAfterUInt256, MachineState.activeWordsAfter]

@[simp] private theorem readPadded_empty_zero (start : Nat) :
    MachineState.readPadded ByteArray.empty start 0 = ByteArray.empty := by
  apply ByteArray.ext
  simp [MachineState.readPadded]

@[simp] private theorem jump1237 :
    Decode.isValidJumpDest referenceBytecode 1237 = true :=
  Artifact.isValidJumpDest_index 928 (by rfl)

@[simp] private theorem jump517 :
    Decode.isValidJumpDest referenceBytecode 517 = true :=
  Artifact.isValidJumpDest_index 415 (by rfl)

def zeroSizeFinalState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1236
    stack := [UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)]
    halt := .Returned
    hReturn := ByteArray.empty }

def zeroSetupState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1236
    stack := [0, 0, UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def wordDispatchState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1237
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def wordCheckedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1253
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Calling-convention state at the first instruction of `modexpWord`. -/
def wordEntryState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 517
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1267, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem run_zeroSetup (input : ByteArray) (hzero : modulusSize input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroSetupPath
      (Main.headerState input) = some (zeroSetupState input) := by
  simp (config := { maxSteps := 200000 })
    [zeroSetupPath, zeroSizePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Main.headerState, zeroSetupState, initialState, hzero, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]; rfl

set_option linter.unusedSimpArgs false in
theorem run_zeroReturn (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroReturnPath
      (zeroSetupState input) = some (zeroSizeFinalState input) := by
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp [zeroReturnPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    zeroSetupState, zeroSizeFinalState, Main.headerState, initialState,
    Challenge.EvmProof.Word.word_toNat_ofNat, h0, hzeroWord]

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem run_wordJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordJumpPath
      (Main.headerState input) = some (wordDispatchState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hmodNat : modulusSize input % 2 ^ 256 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hm']
    omega
  norm_num at hmodNat
  have h1237 : (1237 : UInt256).toNat = 1237 := by decide
  have h1237Word : (1237 : UInt256) = UInt256.ofNat 1237 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat (modulusSize input)) := by
    exact hmodNat
  simp [wordJumpPath, wordEntryPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Main.headerState, wordDispatchState, initialState, hmodNat, h1237,
    h1237Word, htrue,
    UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem run_wordRest (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordCheckPath
      (wordDispatchState input) = some (wordCheckedState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb' : baseSize input < 2 ^ 256 := by omega
  have he' : exponentSize input < 2 ^ 256 := by omega
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hexp : 96 + baseSize input < 2 ^ 256 := by omega
  have hmod : 96 + baseSize input + exponentSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm'
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hgt : UInt256.gt (UInt256.ofNat (modulusSize input)) 32 = 0 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h32]
    have hle : modulusSize input % 2 ^ 256 ≤ 32 :=
      (Nat.mod_le (modulusSize input) (2 ^ 256)).trans hword
    rw [if_neg (Nat.not_lt.mpr hle)]
    rfl
  have hadd₁ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 96) (b := baseSize input) hexp
  have hadd₂ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := exponentSize input) (b := 96 + baseSize input) (by omega)
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  simp (config := { maxSteps := 300000 })
    [wordCheckPath, wordRestPath, wordEntryPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      wordDispatchState, wordCheckedState, Main.headerState, initialState,
      UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      hb', he', hm', hexp, hmod, hpositive, hword, hmmod, h32,
      hgt, h0, hzeroWord, h96Word,
      hadd₁, hadd₂, Nat.add_assoc]

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem run_wordTail (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordTailPath
      (wordCheckedState input) = some (wordEntryState input) := by
  have h517 : (517 : UInt256).toNat = 517 := by decide
  have h517Word : (517 : UInt256) = UInt256.ofNat 517 := by decide
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  have h1267Word : (1267 : UInt256) = UInt256.ofNat 1267 := by decide
  simp (config := { maxSteps := 200000 })
    [wordTailPath, wordRestPath, wordEntryPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      wordCheckedState, wordEntryState, Main.headerState, initialState,
      h517, h517Word, h96Word, h1267Word,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

private def gasSteps_zeroSetup (input : ByteArray)
    (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (zeroSetupState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka zeroSetupPath rfl rfl
      (run_zeroSetup input hzero) rfl deployAddress_not_precompile

private def gasSteps_zeroReturn (input : ByteArray) :
    Challenge.EvmProof.GasSteps (zeroSetupState input)
      (zeroSizeFinalState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka zeroReturnPath rfl rfl
      (run_zeroReturn input) rfl deployAddress_not_precompile

private theorem gasSteps_zeroSetup_cost (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (gasSteps_zeroSetup input hzero).cost = 21 := by
  unfold gasSteps_zeroSetup
  change Challenge.EvmProof.Stepper.runLocatedBlockCost zeroSetupPath
      (Main.headerState input) = 21
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    zeroSetupPath, zeroSizePath, opAt, pushAt,
    Challenge.EvmProof.Stepper.instrCost, Gas.baseCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Main.headerState, initialState,
    hzero, UInt256.isTrue, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

@[simp] private theorem gasSteps_zeroReturn_cost (input : ByteArray) :
    (gasSteps_zeroReturn input).cost = 0 := by
  have h0 : (0 : UInt256).toNat = 0 := by decide
  unfold gasSteps_zeroReturn
  change Challenge.EvmProof.Stepper.runLocatedBlockCost zeroReturnPath
      (zeroSetupState input) = 0
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    zeroReturnPath, opAt, Challenge.EvmProof.Stepper.instrCost,
    Gas.totalCost, Gas.returnTotal, Gas.baseCost,
    MachineState.memExpansionDelta, MachineState.activeWordsAfter,
    zeroSetupState, h0]

def gasSteps_zeroSize (input : ByteArray) (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (zeroSizeFinalState input) :=
  (gasSteps_zeroSetup input hzero).trans (gasSteps_zeroReturn input)

set_option maxHeartbeats 5000000 in
theorem gasSteps_zeroSize_cost (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (gasSteps_zeroSize input hzero).cost = 21 := by
  simp [gasSteps_zeroSize, gasSteps_zeroSetup_cost]

private def gasSteps_wordJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (wordDispatchState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka wordJumpPath rfl rfl
      (run_wordJump input hvalid hpositive) rfl deployAddress_not_precompile

private def gasSteps_wordCheck (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (wordDispatchState input)
      (wordCheckedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka wordCheckPath rfl rfl
      (run_wordRest input hvalid hpositive hword) rfl deployAddress_not_precompile

private def gasSteps_wordTail (input : ByteArray) :
    Challenge.EvmProof.GasSteps (wordCheckedState input)
      (wordEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka wordTailPath rfl rfl
      (run_wordTail input) rfl deployAddress_not_precompile

@[simp] private theorem gasSteps_wordJump_cost (input : ByteArray)
    (hvalid : ValidInput input) (hpositive : 0 < modulusSize input) :
    (gasSteps_wordJump input hvalid hpositive).cost = 17 := by rfl

@[simp] private theorem gasSteps_wordCheck_cost (input : ByteArray)
    (hvalid : ValidInput input) (hpositive : 0 < modulusSize input)
    (hword : modulusSize input ≤ 32) :
    (gasSteps_wordCheck input hvalid hpositive hword).cost = 41 := by rfl

@[simp] private theorem gasSteps_wordTail_cost (input : ByteArray) :
    (gasSteps_wordTail input).cost = 32 := by rfl

def gasSteps_wordEntry (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (wordEntryState input) :=
  (gasSteps_wordJump input hvalid hpositive).trans <|
    (gasSteps_wordCheck input hvalid hpositive hword).trans
      (gasSteps_wordTail input)

set_option maxHeartbeats 5000000 in
theorem gasSteps_wordEntry_cost (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    (gasSteps_wordEntry input hvalid hpositive hword).cost = 90 := by
  simp [gasSteps_wordEntry]

/-- Complete trace and exact minimum gas for zero-width results. -/
def gasSteps_zeroSize_total (input : ByteArray) (hvalid : ValidInput input)
    (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (zeroSizeFinalState input) :=
  (Main.gasSteps_header input hvalid).trans (gasSteps_zeroSize input hzero)

theorem gasSteps_zeroSize_total_cost (input : ByteArray)
    (hvalid : ValidInput input) (hzero : modulusSize input = 0) :
    (gasSteps_zeroSize_total input hvalid hzero).cost = 183 := by
  simp [gasSteps_zeroSize_total, Main.gasSteps_header_cost,
    gasSteps_zeroSize_cost]

@[simp] theorem zeroSizeFinalState_isDone (input : ByteArray) :
    (zeroSizeFinalState input).isDone = true := by
  rfl

theorem zeroSizeFinalState_result (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (zeroSizeFinalState input).toResult = .returned (spec input) := by
  simp [zeroSizeFinalState, spec, hzero]

end Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch
