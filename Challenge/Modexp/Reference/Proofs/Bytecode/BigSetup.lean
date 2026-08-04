import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
import Challenge.Modexp.Reference.Proofs.Bytecode.BigLoadCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-!
# Certified multi-limb MODEXP initialization

The general path computes its limb count, clears the modulus, base,
accumulator, and output buffers, then loads the big-endian modulus into the
little-endian modulus buffer.  This file composes the already-certified
`clearLimbs` and `loadBigEndian` helpers at their concrete call sites.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigSetup

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def wfOp {op : Operation}
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
    (hget : Artifact.referenceInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def setupToClear0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 563 .JUMPDEST, pushAt 564 1 31,
   opAt 565 (.Dup ⟨3, by decide⟩), opAt 566 .ADD,
   pushAt 567 1 5, opAt 568 .SHR, pushAt 569 2 721,
   opAt 570 (.Dup ⟨1, by decide⟩), pushAt 571 0 0,
   pushAt 572 2 19, opAt 573 .JUMP]

def toClear1024Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 574 .JUMPDEST, pushAt 575 2 733,
   opAt 576 (.Dup ⟨1, by decide⟩), pushAt 577 2 1024,
   pushAt 578 2 19, opAt 579 .JUMP]

def toClear2048Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 580 .JUMPDEST, pushAt 581 2 745,
   opAt 582 (.Dup ⟨1, by decide⟩), pushAt 583 2 2048,
   pushAt 584 2 19, opAt 585 .JUMP]

def toClear6144Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 586 .JUMPDEST, pushAt 587 2 757,
   opAt 588 (.Dup ⟨1, by decide⟩), pushAt 589 2 6144,
   pushAt 590 2 19, opAt 591 .JUMP]

def toLoadModulusPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 592 .JUMPDEST, pushAt 593 2 768, pushAt 594 0 0,
   opAt 595 (.Dup ⟨5, by decide⟩), opAt 596 (.Dup ⟨9, by decide⟩),
   pushAt 597 2 439, opAt 598 .JUMP]

def saved (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat (Limbs.limbCount m), UInt256.ofNat b, UInt256.ofNat e,
    UInt256.ofNat m, UInt256.ofNat baseOff, UInt256.ofNat expOff,
    UInt256.ofNat modOff, returnDest] ++ rest

def setupEntry (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 704
           stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff,
             UInt256.ofNat modOff, returnDest] ++ rest }

def afterClear0 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  BigHelpers.clearReturned s 0 (Limbs.limbCount m) 721
    (saved b e m baseOff expOff modOff returnDest rest)

def afterClear1024 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  BigHelpers.clearReturned
    (afterClear0 s b e m baseOff expOff modOff returnDest rest)
    1024 (Limbs.limbCount m) 733
    (saved b e m baseOff expOff modOff returnDest rest)

def afterClear2048 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  BigHelpers.clearReturned
    (afterClear1024 s b e m baseOff expOff modOff returnDest rest)
    2048 (Limbs.limbCount m) 745
    (saved b e m baseOff expOff modOff returnDest rest)

def afterClear6144 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  BigHelpers.clearReturned
    (afterClear2048 s b e m baseOff expOff modOff returnDest rest)
    6144 (Limbs.limbCount m) 757
    (saved b e m baseOff expOff modOff returnDest rest)

def setupReturned (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  BigLoad.loadReturned
    (afterClear6144 s b e m baseOff expOff modOff returnDest rest)
    (UInt256.ofNat modOff) (UInt256.ofNat m) 0 768
    (saved b e m baseOff expOff modOff returnDest rest)

@[simp] private theorem setupPCs (i : Nat) (hi : 563 ≤ i)
    (hii : i ≤ 598) :
    Artifact.referenceArtifact.instructionPC i =
      [704,705,707,708,709,711,712,715,716,717,720,721,722,725,726,
       729,732,733,734,737,738,741,744,745,746,749,750,753,756,757,
       758,761,762,763,764,767][i - 563]! := by
  interval_cases i <;> decide

private theorem jump19 :
    Decode.isValidJumpDest referenceBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump439 :
    Decode.isValidJumpDest referenceBytecode 439 = true :=
  Artifact.isValidJumpDest_index 353 (by rfl)

private theorem jump721 :
    Decode.isValidJumpDest referenceBytecode 721 = true :=
  Artifact.isValidJumpDest_index 574 (by rfl)

private theorem jump733 :
    Decode.isValidJumpDest referenceBytecode 733 = true :=
  Artifact.isValidJumpDest_index 580 (by rfl)

private theorem jump745 :
    Decode.isValidJumpDest referenceBytecode 745 = true :=
  Artifact.isValidJumpDest_index 586 (by rfl)

private theorem jump757 :
    Decode.isValidJumpDest referenceBytecode 757 = true :=
  Artifact.isValidJumpDest_index 592 (by rfl)

private theorem jump768 :
    Decode.isValidJumpDest referenceBytecode 768 = true :=
  Artifact.isValidJumpDest_index 599 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_setupToClear0 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hm : m ≤ 1024) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupToClear0Path
      (setupEntry s b e m baseOff expOff modOff returnDest rest) =
        some (BigHelpers.clearEntry s 0 (Limbs.limbCount m) 721
          (saved b e m baseOff expOff modOff returnDest rest)) := by
  have hm256 : m < 2 ^ 256 := by omega
  have haddFit : m + 31 < 2 ^ 256 := by omega
  have hcountFit : Limbs.limbCount m < 2 ^ 256 := by
    have := Limbs.limbCount_le_32 m hm
    omega
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := m + 31) (shift := 5) haddFit (by norm_num)
  have hdiv : (m + 31) >>> 5 = Limbs.limbCount m := by
    rw [Nat.shiftRight_eq_div_pow]
    rfl
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h5Word : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h19 : (19 : UInt256).toNat = 19 := by decide
  have h19Word : (19 : UInt256) = UInt256.ofNat 19 := by decide
  have h31Word : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h721Word : (721 : UInt256) = UInt256.ofNat 721 := by decide
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp (config := { maxSteps := 350000 }) (discharger := omega)
    [setupToClear0Path, opAt, pushAt, wfOp, setupEntry,
      BigHelpers.clearEntry, saved, setupPCs, jump19, hrun, hshift, hdiv,
      hzero, h0Word, h5Word, h19, h19Word, h31Word, h721Word, hcode,
      hcap, hcountFit, hc7, hc8, hc9, hc10, hc11, hc12,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat haddFit,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt,
      Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_toClear1024 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClear1024Path
      (afterClear0 s b e m baseOff expOff modOff returnDest rest) =
        some (BigHelpers.clearEntry
          (afterClear0 s b e m baseOff expOff modOff returnDest rest)
          1024 (Limbs.limbCount m) 733
          (saved b e m baseOff expOff modOff returnDest rest)) := by
  have h721 : (721 : UInt256).toNat = 721 := by decide
  have h721Word : (721 : UInt256) = UInt256.ofNat 721 := by decide
  have h19 : (19 : UInt256).toNat = 19 := by decide
  have h19Word : (19 : UInt256) = UInt256.ofNat 19 := by decide
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp (config := { maxSteps := 250000 }) (discharger := omega)
    [toClear1024Path, opAt, pushAt, wfOp, afterClear0,
      BigHelpers.clearReturned, BigHelpers.clearEntry, saved, setupPCs,
      jump19, hcap, hcode, hrun, h721, h721Word, h19, h19Word,
      hc8, hc9, hc10, hc11, hc12,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_toClear2048 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClear2048Path
      (afterClear1024 s b e m baseOff expOff modOff returnDest rest) =
        some (BigHelpers.clearEntry
          (afterClear1024 s b e m baseOff expOff modOff returnDest rest)
          2048 (Limbs.limbCount m) 745
          (saved b e m baseOff expOff modOff returnDest rest)) := by
  have h733 : (733 : UInt256).toNat = 733 := by decide
  have h733Word : (733 : UInt256) = UInt256.ofNat 733 := by decide
  have h19 : (19 : UInt256).toNat = 19 := by decide
  have h19Word : (19 : UInt256) = UInt256.ofNat 19 := by decide
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp (config := { maxSteps := 250000 }) (discharger := omega)
    [toClear2048Path, opAt, pushAt, wfOp, afterClear1024, afterClear0,
      BigHelpers.clearReturned, BigHelpers.clearEntry, saved, setupPCs,
      jump19, hcap, hcode, hrun, h733, h733Word, h19, h19Word,
      hc8, hc9, hc10, hc11, hc12,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_toClear6144 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClear6144Path
      (afterClear2048 s b e m baseOff expOff modOff returnDest rest) =
        some (BigHelpers.clearEntry
          (afterClear2048 s b e m baseOff expOff modOff returnDest rest)
          6144 (Limbs.limbCount m) 757
          (saved b e m baseOff expOff modOff returnDest rest)) := by
  have h745 : (745 : UInt256).toNat = 745 := by decide
  have h745Word : (745 : UInt256) = UInt256.ofNat 745 := by decide
  have h19 : (19 : UInt256).toNat = 19 := by decide
  have h19Word : (19 : UInt256) = UInt256.ofNat 19 := by decide
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp (config := { maxSteps := 250000 }) (discharger := omega)
    [toClear6144Path, opAt, pushAt, wfOp, afterClear2048, afterClear1024,
      afterClear0, BigHelpers.clearReturned, BigHelpers.clearEntry, saved,
      setupPCs, jump19, hcap, hcode, hrun, h745, h745Word, h19, h19Word,
      hc8, hc9, hc10, hc11, hc12,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_toLoadModulus (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (_hm : m < 2 ^ 256) (_hmodOff : modOff < 2 ^ 256)
    (hcap : rest.length < 992)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toLoadModulusPath
      (afterClear6144 s b e m baseOff expOff modOff returnDest rest) =
        some (BigLoad.loadEntry
          (afterClear6144 s b e m baseOff expOff modOff returnDest rest)
          (UInt256.ofNat modOff) (UInt256.ofNat m) 0 768
          (saved b e m baseOff expOff modOff returnDest rest)) := by
  have h757 : (757 : UInt256).toNat = 757 := by decide
  have h757Word : (757 : UInt256) = UInt256.ofNat 757 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h439 : (439 : UInt256).toNat = 439 := by decide
  have h439Word : (439 : UInt256) = UInt256.ofNat 439 := by decide
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [toLoadModulusPath, opAt, pushAt, wfOp, afterClear6144,
      afterClear2048, afterClear1024, afterClear0, BigHelpers.clearReturned,
      BigLoad.loadEntry, saved, setupPCs, jump439, hcap, h757,
      h757Word, hzero, h0Word, h439, h439Word, hcode, hrun,
      hc8, hc9, hc10, hc11, hc12, hc13,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt,
      Nat.add_assoc]

def gasSteps_setupToClear0 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hm : m ≤ 1024) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (setupEntry s b e m baseOff expOff modOff returnDest rest)
      (BigHelpers.clearEntry s 0 (Limbs.limbCount m) 721
        (saved b e m baseOff expOff modOff returnDest rest)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka setupToClear0Path
      (by simpa [setupEntry, Artifact.referenceArtifact] using hcode)
      (by simpa [setupEntry, State.fork] using hfork)
      (run_setupToClear0 s b e m baseOff expOff modOff returnDest rest
        hm hcap hcode hrun)
      (by simpa [setupEntry] using hrun)
      (by simpa [setupEntry, State.fork] using hnp)

def gasSteps_toClear1024 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (afterClear0 s b e m baseOff expOff modOff returnDest rest)
      (BigHelpers.clearEntry
        (afterClear0 s b e m baseOff expOff modOff returnDest rest)
        1024 (Limbs.limbCount m) 733
        (saved b e m baseOff expOff modOff returnDest rest)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka toClear1024Path
      (by simpa [afterClear0, BigHelpers.clearReturned,
        Artifact.referenceArtifact] using hcode)
      (by simpa [afterClear0, BigHelpers.clearReturned, State.fork] using hfork)
      (run_toClear1024 s b e m baseOff expOff modOff returnDest rest
        hcap hcode hrun)
      (by simpa [afterClear0, BigHelpers.clearReturned] using hrun)
      (by simpa [afterClear0, BigHelpers.clearReturned, State.fork] using hnp)

def gasSteps_toClear2048 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (afterClear1024 s b e m baseOff expOff modOff returnDest rest)
      (BigHelpers.clearEntry
        (afterClear1024 s b e m baseOff expOff modOff returnDest rest)
        2048 (Limbs.limbCount m) 745
        (saved b e m baseOff expOff modOff returnDest rest)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka toClear2048Path
      (by simpa [afterClear1024, afterClear0, BigHelpers.clearReturned,
        Artifact.referenceArtifact] using hcode)
      (by simpa [afterClear1024, afterClear0, BigHelpers.clearReturned,
        State.fork] using hfork)
      (run_toClear2048 s b e m baseOff expOff modOff returnDest rest
        hcap hcode hrun)
      (by simpa [afterClear1024, afterClear0,
        BigHelpers.clearReturned] using hrun)
      (by simpa [afterClear1024, afterClear0, BigHelpers.clearReturned,
        State.fork] using hnp)

def gasSteps_toClear6144 (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (afterClear2048 s b e m baseOff expOff modOff returnDest rest)
      (BigHelpers.clearEntry
        (afterClear2048 s b e m baseOff expOff modOff returnDest rest)
        6144 (Limbs.limbCount m) 757
        (saved b e m baseOff expOff modOff returnDest rest)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka toClear6144Path
      (by simpa [afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, Artifact.referenceArtifact] using hcode)
      (by simpa [afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, State.fork] using hfork)
      (run_toClear6144 s b e m baseOff expOff modOff returnDest rest
        hcap hcode hrun)
      (by simpa [afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned] using hrun)
      (by simpa [afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, State.fork] using hnp)

def gasSteps_toLoadModulus (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hm : m < 2 ^ 256) (hmodOff : modOff < 2 ^ 256)
    (hcap : rest.length < 992)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (afterClear6144 s b e m baseOff expOff modOff returnDest rest)
      (BigLoad.loadEntry
        (afterClear6144 s b e m baseOff expOff modOff returnDest rest)
        (UInt256.ofNat modOff) (UInt256.ofNat m) 0 768
        (saved b e m baseOff expOff modOff returnDest rest)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka toLoadModulusPath
      (by simpa [afterClear6144, afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, Artifact.referenceArtifact] using hcode)
      (by simpa [afterClear6144, afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, State.fork] using hfork)
      (run_toLoadModulus s b e m baseOff expOff modOff returnDest rest
        hm hmodOff hcap hcode hrun)
      (by simpa [afterClear6144, afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned] using hrun)
      (by simpa [afterClear6144, afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, State.fork] using hnp)

theorem gasSteps_setupToClear0_cost (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hm : m ≤ 1024) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_setupToClear0 s b e m baseOff expOff modOff returnDest rest
      hm hcap hcode hfork hrun hnp).cost = 35 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    setupToClear0Path 35
      (run_setupToClear0 s b e m baseOff expOff modOff returnDest rest
        hm hcap hcode hrun)
      (by simpa [setupEntry, State.fork] using hfork)
      (by decide) (by decide)
  have hactive :
      (setupEntry s b e m baseOff expOff modOff returnDest rest).activeWords =
      (BigHelpers.clearEntry s 0 (Limbs.limbCount m) 721
        (saved b e m baseOff expOff modOff returnDest rest)).activeWords := by
    rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost
      setupToClear0Path
        (setupEntry s b e m baseOff expOff modOff returnDest rest) = 35 := by
    omega
  simpa [gasSteps_setupToClear0] using hcost

theorem gasSteps_toClear1024_cost (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_toClear1024 s b e m baseOff expOff modOff returnDest rest
      hcap hcode hfork hrun hnp).cost = 21 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    toClear1024Path 21
      (run_toClear1024 s b e m baseOff expOff modOff returnDest rest
        hcap hcode hrun)
      (by simpa [afterClear0, BigHelpers.clearReturned, State.fork] using hfork)
      (by decide) (by decide)
  have hactive :
      (afterClear0 s b e m baseOff expOff modOff returnDest rest).activeWords =
      (BigHelpers.clearEntry
        (afterClear0 s b e m baseOff expOff modOff returnDest rest)
        1024 (Limbs.limbCount m) 733
        (saved b e m baseOff expOff modOff returnDest rest)).activeWords := by
    rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost
      toClear1024Path
        (afterClear0 s b e m baseOff expOff modOff returnDest rest) = 21 := by
    omega
  simpa [gasSteps_toClear1024] using hcost

theorem gasSteps_toClear2048_cost (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_toClear2048 s b e m baseOff expOff modOff returnDest rest
      hcap hcode hfork hrun hnp).cost = 21 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    toClear2048Path 21
      (run_toClear2048 s b e m baseOff expOff modOff returnDest rest
        hcap hcode hrun)
      (by simpa [afterClear1024, afterClear0, BigHelpers.clearReturned,
        State.fork] using hfork)
      (by decide) (by decide)
  have hactive :
      (afterClear1024 s b e m baseOff expOff modOff returnDest rest).activeWords =
      (BigHelpers.clearEntry
        (afterClear1024 s b e m baseOff expOff modOff returnDest rest)
        2048 (Limbs.limbCount m) 745
        (saved b e m baseOff expOff modOff returnDest rest)).activeWords := by
    rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost
      toClear2048Path
        (afterClear1024 s b e m baseOff expOff modOff returnDest rest) = 21 := by
    omega
  simpa [gasSteps_toClear2048] using hcost

theorem gasSteps_toClear6144_cost (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_toClear6144 s b e m baseOff expOff modOff returnDest rest
      hcap hcode hfork hrun hnp).cost = 21 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    toClear6144Path 21
      (run_toClear6144 s b e m baseOff expOff modOff returnDest rest
        hcap hcode hrun)
      (by simpa [afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, State.fork] using hfork)
      (by decide) (by decide)
  have hactive :
      (afterClear2048 s b e m baseOff expOff modOff returnDest rest).activeWords =
      (BigHelpers.clearEntry
        (afterClear2048 s b e m baseOff expOff modOff returnDest rest)
        6144 (Limbs.limbCount m) 757
        (saved b e m baseOff expOff modOff returnDest rest)).activeWords := by
    rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost
      toClear6144Path
        (afterClear2048 s b e m baseOff expOff modOff returnDest rest) = 21 := by
    omega
  simpa [gasSteps_toClear6144] using hcost

theorem gasSteps_toLoadModulus_cost (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hm : m < 2 ^ 256)
    (hmodOff : modOff < 2 ^ 256) (hcap : rest.length < 992)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_toLoadModulus s b e m baseOff expOff modOff returnDest rest
      hm hmodOff hcap hcode hfork hrun hnp).cost = 23 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    toLoadModulusPath 23
      (run_toLoadModulus s b e m baseOff expOff modOff returnDest rest
        hm hmodOff hcap hcode hrun)
      (by simpa [afterClear6144, afterClear2048, afterClear1024, afterClear0,
        BigHelpers.clearReturned, State.fork] using hfork)
      (by decide) (by decide)
  have hactive :
      (afterClear6144 s b e m baseOff expOff modOff returnDest rest).activeWords =
      (BigLoad.loadEntry
        (afterClear6144 s b e m baseOff expOff modOff returnDest rest)
        (UInt256.ofNat modOff) (UInt256.ofNat m) 0 768
        (saved b e m baseOff expOff modOff returnDest rest)).activeWords := by
    rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost
      toLoadModulusPath
        (afterClear6144 s b e m baseOff expOff modOff returnDest rest) = 23 := by
    omega
  simpa [gasSteps_toLoadModulus] using hcost

def gasSteps_setup (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hmBound : m ≤ 1024) (hmodOff : modOff < 2 ^ 256)
    (hinputFit : modOff + m ≤ 2 ^ 256) (hcap : rest.length < 992)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (setupEntry s b e m baseOff expOff modOff returnDest rest)
      (setupReturned s b e m baseOff expOff modOff returnDest rest) := by
  let frame := saved b e m baseOff expOff modOff returnDest rest
  have hm : m < 2 ^ 256 := by omega
  have hn : Limbs.limbCount m < 2 ^ 256 := by
    have := Limbs.limbCount_le_32 m hmBound
    omega
  have hframeClear : frame.length < 1017 := by
    simp [frame, saved]
    omega
  have hframeLoad : frame.length < 1000 := by
    simp [frame, saved]
    omega
  have hcapSetup : rest.length < 1010 := by omega
  let s0 := afterClear0 s b e m baseOff expOff modOff returnDest rest
  let s1 := afterClear1024 s b e m baseOff expOff modOff returnDest rest
  let s2 := afterClear2048 s b e m baseOff expOff modOff returnDest rest
  let s3 := afterClear6144 s b e m baseOff expOff modOff returnDest rest
  have hcode0 : s0.executionEnv.code = referenceBytecode := by
    simpa [s0, afterClear0, BigHelpers.clearReturned] using hcode
  have hcode1 : s1.executionEnv.code = referenceBytecode := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hcode
  have hcode2 : s2.executionEnv.code = referenceBytecode := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hcode
  have hcode3 : s3.executionEnv.code = referenceBytecode := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned] using hcode
  have hfork0 : s0.fork = .Osaka := by
    simpa [s0, afterClear0, BigHelpers.clearReturned, State.fork] using hfork
  have hfork1 : s1.fork = .Osaka := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hfork
  have hfork2 : s2.fork = .Osaka := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hfork
  have hfork3 : s3.fork = .Osaka := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned, State.fork] using hfork
  have hrun0 : s0.halt = .Running := by
    simpa [s0, afterClear0, BigHelpers.clearReturned] using hrun
  have hrun1 : s1.halt = .Running := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hrun
  have hrun2 : s2.halt = .Running := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hrun
  have hrun3 : s3.halt = .Running := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned] using hrun
  have hnp0 : Precompile.isPrecompile s0.executionEnv.fork
      s0.executionEnv.codeAddr = false := by
    simpa [s0, afterClear0, BigHelpers.clearReturned, State.fork] using hnp
  have hnp1 : Precompile.isPrecompile s1.executionEnv.fork
      s1.executionEnv.codeAddr = false := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hnp
  have hnp2 : Precompile.isPrecompile s2.executionEnv.fork
      s2.executionEnv.codeAddr = false := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hnp
  have hnp3 : Precompile.isPrecompile s3.executionEnv.fork
      s3.executionEnv.codeAddr = false := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned, State.fork] using hnp
  exact
    (gasSteps_setupToClear0 s b e m baseOff expOff modOff returnDest rest
      hmBound hcapSetup hcode hfork hrun hnp).trans <|
    (BigHelpers.gasSteps_clear s 0 (Limbs.limbCount m) 721 frame
      hframeClear hn hcode hfork hrun hnp jump721).trans <|
    (gasSteps_toClear1024 s b e m baseOff expOff modOff returnDest rest
      hcapSetup hcode hfork hrun hnp).trans <|
    (BigHelpers.gasSteps_clear s0 1024 (Limbs.limbCount m) 733 frame
      hframeClear hn hcode0 hfork0 hrun0 hnp0 jump733).trans <|
    (gasSteps_toClear2048 s b e m baseOff expOff modOff returnDest rest
      hcapSetup hcode hfork hrun hnp).trans <|
    (BigHelpers.gasSteps_clear s1 2048 (Limbs.limbCount m) 745 frame
      hframeClear hn hcode1 hfork1 hrun1 hnp1 jump745).trans <|
    (gasSteps_toClear6144 s b e m baseOff expOff modOff returnDest rest
      hcapSetup hcode hfork hrun hnp).trans <|
    (BigHelpers.gasSteps_clear s2 6144 (Limbs.limbCount m) 757 frame
      hframeClear hn hcode2 hfork2 hrun2 hnp2 jump757).trans <|
    (gasSteps_toLoadModulus s b e m baseOff expOff modOff returnDest rest
      hm hmodOff hcap hcode hfork hrun hnp).trans <|
    BigLoad.gasSteps_loadBigEndian s3 modOff m 0 768 frame hframeLoad
      hmodOff hinputFit hm hcode3 hfork3 hrun3 hnp3 jump768

theorem gasSteps_setup_cost_potential (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hmBound : m ≤ 1024)
    (hmodOff : modOff < 2 ^ 256) (hinputFit : modOff + m ≤ 2 ^ 256)
    (hcap : rest.length < 992)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_setup s b e m baseOff expOff modOff returnDest rest hmBound
        hmodOff hinputFit hcap hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      (343 + Limbs.limbCount m * 284 + m * 190) +
        MachineState.memCost
          (setupReturned s b e m baseOff expOff modOff returnDest rest).activeWords.toNat := by
  let frame := saved b e m baseOff expOff modOff returnDest rest
  let n := Limbs.limbCount m
  let s0 := afterClear0 s b e m baseOff expOff modOff returnDest rest
  let s1 := afterClear1024 s b e m baseOff expOff modOff returnDest rest
  let s2 := afterClear2048 s b e m baseOff expOff modOff returnDest rest
  let s3 := afterClear6144 s b e m baseOff expOff modOff returnDest rest
  have hm : m < 2 ^ 256 := by omega
  have hn : n < 2 ^ 256 := by
    have := Limbs.limbCount_le_32 m hmBound
    omega
  have hframeClear : frame.length < 1017 := by
    simp [frame, saved]
    omega
  have hframeLoad : frame.length < 1000 := by
    simp [frame, saved]
    omega
  have hcapSetup : rest.length < 1010 := by omega
  have hcode0 : s0.executionEnv.code = referenceBytecode := by
    simpa [s0, afterClear0, BigHelpers.clearReturned] using hcode
  have hcode1 : s1.executionEnv.code = referenceBytecode := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hcode
  have hcode2 : s2.executionEnv.code = referenceBytecode := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hcode
  have hcode3 : s3.executionEnv.code = referenceBytecode := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned] using hcode
  have hfork0 : s0.fork = .Osaka := by
    simpa [s0, afterClear0, BigHelpers.clearReturned, State.fork] using hfork
  have hfork1 : s1.fork = .Osaka := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hfork
  have hfork2 : s2.fork = .Osaka := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hfork
  have hfork3 : s3.fork = .Osaka := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned, State.fork] using hfork
  have hrun0 : s0.halt = .Running := by
    simpa [s0, afterClear0, BigHelpers.clearReturned] using hrun
  have hrun1 : s1.halt = .Running := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hrun
  have hrun2 : s2.halt = .Running := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned] using hrun
  have hrun3 : s3.halt = .Running := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned] using hrun
  have hnp0 : Precompile.isPrecompile s0.executionEnv.fork
      s0.executionEnv.codeAddr = false := by
    simpa [s0, afterClear0, BigHelpers.clearReturned, State.fork] using hnp
  have hnp1 : Precompile.isPrecompile s1.executionEnv.fork
      s1.executionEnv.codeAddr = false := by
    simpa [s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hnp
  have hnp2 : Precompile.isPrecompile s2.executionEnv.fork
      s2.executionEnv.codeAddr = false := by
    simpa [s2, afterClear2048, s1, afterClear1024, s0, afterClear0,
      BigHelpers.clearReturned, State.fork] using hnp
  have hnp3 : Precompile.isPrecompile s3.executionEnv.fork
      s3.executionEnv.codeAddr = false := by
    simpa [s3, afterClear6144, s2, afterClear2048, s1, afterClear1024,
      s0, afterClear0, BigHelpers.clearReturned, State.fork] using hnp
  have hr0 := gasSteps_setupToClear0_cost s b e m baseOff expOff modOff
    returnDest rest hmBound hcapSetup hcode hfork hrun hnp
  have hr1 := gasSteps_toClear1024_cost s b e m baseOff expOff modOff
    returnDest rest hcapSetup hcode hfork hrun hnp
  have hr2 := gasSteps_toClear2048_cost s b e m baseOff expOff modOff
    returnDest rest hcapSetup hcode hfork hrun hnp
  have hr3 := gasSteps_toClear6144_cost s b e m baseOff expOff modOff
    returnDest rest hcapSetup hcode hfork hrun hnp
  have hr4 := gasSteps_toLoadModulus_cost s b e m baseOff expOff modOff
    returnDest rest hm hmodOff hcap hcode hfork hrun hnp
  have hc0 := BigHelpers.gasSteps_clear_cost_potential s 0 n 721 frame
    hframeClear hn hcode hfork hrun hnp jump721
  have hc1 := BigHelpers.gasSteps_clear_cost_potential s0 1024 n 733 frame
    hframeClear hn hcode0 hfork0 hrun0 hnp0 jump733
  have hc2 := BigHelpers.gasSteps_clear_cost_potential s1 2048 n 745 frame
    hframeClear hn hcode1 hfork1 hrun1 hnp1 jump745
  have hc3 := BigHelpers.gasSteps_clear_cost_potential s2 6144 n 757 frame
    hframeClear hn hcode2 hfork2 hrun2 hnp2 jump757
  have hl := BigLoad.gasSteps_loadBigEndian_cost_potential s3 modOff m 0 768
    frame hframeLoad hmodOff hinputFit hm hcode3 hfork3 hrun3 hnp3 jump768
  unfold gasSteps_setup
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  rw [hr0, hr1, hr2, hr3, hr4]
  change _ + MachineState.memCost s.activeWords.toNat =
    _ + MachineState.memCost
      (BigLoad.loadReturned s3 (UInt256.ofNat modOff) (UInt256.ofNat m) 0
        768 frame).activeWords.toNat
  simp only [n, frame, s0, s1, s2, s3, afterClear0, afterClear1024,
    afterClear2048, afterClear6144] at hc0 hc1 hc2 hc3 hl
  simp only [frame, s3, afterClear0, afterClear1024, afterClear2048,
    afterClear6144]
  omega

theorem setupReturned_modulus_represents (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hmBound : m ≤ 1024)
    (hmodOff : modOff < 2 ^ 256) :
    Limbs.Represents
      (setupReturned s b e m baseOff expOff modOff returnDest rest).memory
      0 (Limbs.limbCount m)
      (Precompile.bytesToNatPadded s.executionEnv.calldata modOff m) := by
  let n := Limbs.limbCount m
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hfit0 : 0 + 32 * n < 2 ^ 256 := by omega
  have hfit1024 : 1024 + 32 * n < 2 ^ 256 := by omega
  have hfit2048 : 2048 + 32 * n < 2 ^ 256 := by omega
  have hfit6144 : 6144 + 32 * n < 2 ^ 256 := by omega
  have hbefore1024 : 0 + 32 * n ≤ 1024 := by omega
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1024Word : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048Word : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h6144Word : (6144 : UInt256) = UInt256.ofNat 6144 := by decide
  let s0 := afterClear0 s b e m baseOff expOff modOff returnDest rest
  let s1 := afterClear1024 s b e m baseOff expOff modOff returnDest rest
  let s2 := afterClear2048 s b e m baseOff expOff modOff returnDest rest
  let s3 := afterClear6144 s b e m baseOff expOff modOff returnDest rest
  have hz0 : Limbs.Represents s0.memory 0 n 0 := by
    simpa [s0, afterClear0, BigHelpers.clearReturned, n, h0Word] using
      BigHelpers.clearMemory_represents_zero s.memory 0 n hfit0
  have hz1 : Limbs.Represents s1.memory 0 n 0 := by
    have hkeep := BigHelpers.represents_clearMemory_disjoint_region
      s0.memory 1024 0 n 0 hfit1024 (Or.inr hbefore1024) hz0
    simpa [s1, afterClear1024, s0, n, BigHelpers.clearReturned,
      h1024Word] using hkeep
  have hz2 : Limbs.Represents s2.memory 0 n 0 := by
    have hkeep := BigHelpers.represents_clearMemory_disjoint_region
      s1.memory 2048 0 n 0 hfit2048 (Or.inr (by omega)) hz1
    simpa [s2, afterClear2048, s1, n, BigHelpers.clearReturned,
      h2048Word] using hkeep
  have hz3 : Limbs.Represents s3.memory 0 n 0 := by
    have hkeep := BigHelpers.represents_clearMemory_disjoint_region
      s2.memory 6144 0 n 0 hfit6144 (Or.inr (by omega)) hz2
    simpa [s3, afterClear6144, s2, n, BigHelpers.clearReturned,
      h6144Word] using hkeep
  have hm : m < 2 ^ 256 := by omega
  have hloaded := BigLoadCorrect.loadReturned_represents s3 modOff 0 m 768
    (saved b e m baseOff expOff modOff returnDest rest) hmodOff hm hfit0 hz3
  simpa [setupReturned, s3, afterClear6144, afterClear2048,
    afterClear1024, afterClear0, BigHelpers.clearReturned, n, h0Word] using hloaded

end Challenge.Modexp.Reference.Proofs.Bytecode.BigSetup
