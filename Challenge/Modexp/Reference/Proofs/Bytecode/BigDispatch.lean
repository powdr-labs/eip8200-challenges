import Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
/-!
# Multi-limb MODEXP dispatcher

This is the public successful-domain edge for moduli wider than one EVM word.
It packages the compiler calling convention at PC 704 for the general path.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

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
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def bigJumpPath := Dispatch.wordJumpPath

def bigCheckPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 928 .JUMPDEST, opAt 929 (.Dup ⟨2, by decide⟩),
   pushAt 930 1 96, opAt 931 .ADD,
   opAt 932 (.Dup ⟨2, by decide⟩), opAt 933 (.Dup ⟨1, by decide⟩),
   opAt 934 .ADD, pushAt 935 1 32, opAt 936 (.Dup ⟨3, by decide⟩),
   opAt 937 .GT, pushAt 938 2 1268, opAt 939 .JUMPI]

def bigTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 950 .JUMPDEST, pushAt 951 2 1283,
   opAt 952 (.Dup ⟨1, by decide⟩), opAt 953 (.Dup ⟨3, by decide⟩),
   pushAt 954 1 96, opAt 955 (.Dup ⟨6, by decide⟩),
   opAt 956 (.Dup ⟨8, by decide⟩), opAt 957 (.Dup ⟨10, by decide⟩),
   pushAt 958 2 704, opAt 959 .JUMP]

def bigCheckedState (input : ByteArray) : State :=
  { Dispatch.wordCheckedState input with pc := UInt256.ofNat 1268 }

/-- Calling-convention state at the first instruction of `modexpBig`. -/
def bigEntryState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 704
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1283, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

@[simp] private theorem bigTailPCs (i : Nat) (hi : 950 ≤ i)
    (hii : i ≤ 959) :
    Artifact.referenceArtifact.instructionPC i =
      [1268,1269,1272,1273,1274,1276,1277,1278,1279,1282][i - 950]! := by
  interval_cases i <;> decide

private theorem jump704 :
    Decode.isValidJumpDest referenceBytecode 704 = true :=
  Artifact.isValidJumpDest_index 563 (by rfl)

private theorem jump1268 :
    Decode.isValidJumpDest referenceBytecode 1268 = true :=
  Artifact.isValidJumpDest_index 950 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_bigCheck (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckPath
      (Dispatch.wordDispatchState input) = some (bigCheckedState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb' : baseSize input < 2 ^ 256 := by omega
  have he' : exponentSize input < 2 ^ 256 := by omega
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hexp : 96 + baseSize input < 2 ^ 256 := by omega
  have hmod : 96 + baseSize input + exponentSize input < 2 ^ 256 := by omega
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have honeWord : UInt256.ofNat 1 = (1 : UInt256) := by decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  have hgt : UInt256.gt (UInt256.ofNat (modulusSize input)) 32 = 1 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm', h32, if_pos hbig]
    exact honeWord
  have hadd₁ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 96) (b := baseSize input) hexp
  have hadd₂ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := exponentSize input) (b := 96 + baseSize input) (by omega)
  have hadd₂' : UInt256.ofNat (96 + baseSize input) +
      UInt256.ofNat (exponentSize input) =
        UInt256.ofNat (96 + baseSize input + exponentSize input) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1268 : (1268 : UInt256).toNat = 1268 := by decide
  have h1268Word : (1268 : UInt256) = UInt256.ofNat 1268 := by decide
  simp (config := { maxSteps := 350000 })
    [bigCheckPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordDispatchState, Dispatch.wordCheckedState, bigCheckedState,
      Main.headerState, initialState, UInt256.isTrue, hgt, h1268, h1268Word,
      jump1268, hadd₁, hadd₂, hadd₂', honeWord, honeNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      hb', he', hm', hexp, hmod, Nat.add_assoc]
  constructor
  · change UInt256.ofNat 96 + UInt256.ofNat (baseSize input) +
      UInt256.ofNat (exponentSize input) =
        UInt256.ofNat (96 + (baseSize input + exponentSize input))
    rw [hadd₁, hadd₂']
    congr 1
    omega
  · change UInt256.ofNat 96 + UInt256.ofNat (baseSize input) =
      UInt256.ofNat (96 + baseSize input)
    exact hadd₁

set_option linter.unusedSimpArgs false in
theorem run_bigTail (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigTailPath
      (bigCheckedState input) = some (bigEntryState input) := by
  have h704 : (704 : UInt256).toNat = 704 := by decide
  have h704Word : (704 : UInt256) = UInt256.ofNat 704 := by decide
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  have h1283Word : (1283 : UInt256) = UInt256.ofNat 1283 := by decide
  simp (config := { maxSteps := 250000 })
    [bigTailPath, opAt, pushAt, wfOp, bigCheckedState,
      Dispatch.wordCheckedState, bigEntryState, Main.headerState, initialState,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigTailPCs, h704, h704Word, h96Word, h1283Word, jump704,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def gasSteps_bigTail (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigCheckedState input) (bigEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigTailPath rfl rfl
      (run_bigTail input) rfl deployAddress_not_precompile

theorem gasSteps_bigTail_cost (input : ByteArray) :
    (gasSteps_bigTail input).cost = 33 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    bigTailPath 33 (run_bigTail input) (by rfl)
      (by decide) (by decide)
  have hactive : (bigCheckedState input).activeWords =
      (bigEntryState input).activeWords := by rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost bigTailPath
      (bigCheckedState input) = 33 := by omega
  change Challenge.EvmProof.Stepper.runLocatedBlockCost bigTailPath
    (bigCheckedState input) = 33
  exact hcost

def gasSteps_bigCheck (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordDispatchState input)
      (bigCheckedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigCheckPath rfl rfl
      (run_bigCheck input hvalid hbig) rfl deployAddress_not_precompile

theorem gasSteps_bigCheck_cost (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    (gasSteps_bigCheck input hvalid hbig).cost = 41 := by
  rfl

def gasSteps_bigJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (Dispatch.wordDispatchState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka Dispatch.wordJumpPath rfl rfl
      (Dispatch.run_wordJump input hvalid hpositive) rfl
      deployAddress_not_precompile

theorem gasSteps_bigJump_cost (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    (gasSteps_bigJump input hvalid hpositive).cost = 17 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    Dispatch.wordJumpPath 17 (Dispatch.run_wordJump input hvalid hpositive)
      (by rfl) (by decide) (by decide)
  have hactive : (Main.headerState input).activeWords =
      (Dispatch.wordDispatchState input).activeWords := by rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost
      Dispatch.wordJumpPath (Main.headerState input) = 17 := by omega
  change Challenge.EvmProof.Stepper.runLocatedBlockCost Dispatch.wordJumpPath
    (Main.headerState input) = 17
  exact hcost

def gasSteps_bigEntry (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input) (bigEntryState input) :=
  (gasSteps_bigJump input hvalid hpositive).trans <|
    (gasSteps_bigCheck input hvalid hbig).trans (gasSteps_bigTail input)

theorem gasSteps_bigEntry_cost (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hbig : 32 < modulusSize input) :
    (gasSteps_bigEntry input hvalid hpositive hbig).cost = 91 := by
  simp [gasSteps_bigEntry, gasSteps_bigJump_cost, gasSteps_bigCheck_cost,
    gasSteps_bigTail_cost]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
