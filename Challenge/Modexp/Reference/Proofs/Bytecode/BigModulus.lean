import Challenge.Modexp.Reference.Proofs.Bytecode.BigSetup
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-!
# Certified modulus scan

After loading the modulus, the emitted code ORs all modulus limbs.  A zero
accumulator selects the required all-zero result; a nonzero accumulator enters
the modular-exponentiation loops.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigModulus

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

def scanSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 599 .JUMPDEST, pushAt 600 0 0, pushAt 601 0 0]

def scanGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 602 .JUMPDEST, opAt 603 (.Dup ⟨2, by decide⟩),
   opAt 604 (.Dup ⟨1, by decide⟩), opAt 605 .LT, opAt 606 .ISZERO,
   pushAt 607 2 799, opAt 608 .JUMPI]

def scanBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 609 (.Dup ⟨0, by decide⟩), pushAt 610 1 5,
   opAt 611 .SHL, opAt 612 .MLOAD, opAt 613 (.Dup ⟨2, by decide⟩),
   opAt 614 .OR, opAt 615 (.Swap ⟨1, by decide⟩), opAt 616 .POP,
   pushAt 617 1 1, opAt 618 (.Dup ⟨1, by decide⟩), opAt 619 .ADD,
   opAt 620 (.Swap ⟨0, by decide⟩), opAt 621 .POP,
   pushAt 622 2 771, opAt 623 .JUMP]

def scanNonzeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 624 .JUMPDEST, opAt 625 .POP, opAt 626 (.Dup ⟨0, by decide⟩),
   pushAt 627 2 811, opAt 628 .JUMPI]

def scanZeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  scanNonzeroPath ++
    [opAt 629 (.Dup ⟨4, by decide⟩), pushAt 630 2 6144,
     opAt 631 .RETURN]

def scanOr (memory : ByteArray) : Nat → UInt256
  | 0 => 0
  | i + 1 => UInt256.lor (scanOr memory i)
      (MachineState.readWord memory (32 * i))

def scanWords (active : UInt256) : Nat → UInt256
  | 0 => active
  | i + 1 => UInt256.ofNat (MachineState.activeWordsAfter
      (scanWords active i).toNat (32 * i) 32)

def scanEntry (s : State) (count : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 768
           stack := [UInt256.ofNat count] ++ rest }

def scanLoop (s : State) (count i : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 771
           stack := [UInt256.ofNat i, scanOr s.memory i,
             UInt256.ofNat count] ++ rest
           activeWords := scanWords s.activeWords i }

def scanBody (s : State) (count i : Nat) (rest : List UInt256) : State :=
  { scanLoop s count i rest with pc := UInt256.ofNat 780 }

def scanExit (s : State) (count : Nat) (rest : List UInt256) : State :=
  { scanLoop s count count rest with pc := UInt256.ofNat 799 }

def scanNonzero (s : State) (count : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 811
           stack := [scanOr s.memory count, UInt256.ofNat count] ++ rest
           activeWords := scanWords s.activeWords count }

def scanZeroFinal (s : State) (count b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 810
           stack := [0, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff, UInt256.ofNat modOff, returnDest] ++ rest
           activeWords := UInt256.ofNat (MachineState.activeWordsAfter
             (scanWords s.activeWords count).toNat 6144 m)
           halt := .Returned
           hReturn := MachineState.readPadded s.memory 6144 m }

@[simp] private theorem scanPCs (i : Nat) (hi : 599 ≤ i)
    (hii : i ≤ 631) :
    Artifact.referenceArtifact.instructionPC i =
      ([768,769,770,771,772,773,774,775,776,779,780,781,783,784,785,
       786,787,788,789,791,792,793,794,795,798,799,800,801,802,805,
       806,807,810]
        )[i - 599]! := by
  interval_cases i <;> decide

private theorem jump771 :
    Decode.isValidJumpDest referenceBytecode 771 = true :=
  Artifact.isValidJumpDest_index 602 (by rfl)

private theorem jump799 :
    Decode.isValidJumpDest referenceBytecode 799 = true :=
  Artifact.isValidJumpDest_index 624 (by rfl)

private theorem jump811 :
    Decode.isValidJumpDest referenceBytecode 811 = true :=
  Artifact.isValidJumpDest_index 632 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_scanSetup (s : State) (count : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanSetupPath
      (scanEntry s count rest) = some (scanLoop s count 0 rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [scanSetupPath, opAt, pushAt, wfOp, scanEntry, scanLoop, scanOr,
    scanWords, scanPCs, hrun, hc1, hc2, hc3, hzero, h0Word,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_scanGuard (s : State) (count i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanGuardPath
      (scanLoop s count i rest) = some (scanBody s count i rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat count) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount, if_pos hi]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [scanGuardPath, opAt, pushAt, wfOp, scanLoop, scanBody, scanPCs,
    hrun, hc3, hc4, hc5, hlt, honeNat, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_scanBody (s : State) (count i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018) (hcount : count ≤ 32) (hi : i < count)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanBodyPath
      (scanBody s count i rest) = some (scanLoop s count (i + 1) rest) := by
  have hi256 : i < 2 ^ 256 := by omega
  have hiSucc : i + 1 < 2 ^ 256 := by omega
  have haddrFit : i * 2 ^ 5 < 2 ^ 256 := by omega
  have hshift := Challenge.EvmProof.Word.shiftLeft_ofNat
    (value := i) (shift := 5) hi256 (by norm_num) haddrFit
  have haddr : (UInt256.ofNat (i * 2 ^ 5)).toNat = 32 * i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt haddrFit]
    omega
  have haddrMod : i * 32 % 2 ^ 256 = i * 32 := by
    apply Nat.mod_eq_of_lt
    omega
  norm_num at haddrMod
  have haddrModEq := Nat.mod_eq_of_lt haddrMod
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h5Word : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h771 : (771 : UInt256).toNat = 771 := by decide
  have h771Word : (771 : UInt256) = UInt256.ofNat 771 := by decide
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hiSucc
  simp [scanBodyPath, opAt, pushAt, wfOp, scanBody, scanLoop, scanOr,
    scanWords, scanPCs, hrun, hcode, jump771, hshift, haddr, h5Word,
    h771, h771Word, haddrModEq, hone, hinc, hc3, hc4, hc5, hc6,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, State.activeWordsAfterUInt256,
    Nat.add_assoc, Nat.mul_comm, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_scanFinishGuard (s : State) (count : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018) (_hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanGuardPath
      (scanLoop s count count rest) = some (scanExit s count rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h799 : (799 : UInt256).toNat = 799 := by decide
  have h799Word : (799 : UInt256) = UInt256.ofNat 799 := by decide
  simp [scanGuardPath, opAt, pushAt, wfOp, scanLoop, scanExit, scanPCs,
    hrun, hcode, hc3, hc4, hc5, h799, h799Word, jump799,
    UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_scanNonzero (s : State) (count : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018) (hor : scanOr s.memory count ≠ 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanNonzeroPath
      (scanExit s count rest) = some (scanNonzero s count rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have h811 : (811 : UInt256).toNat = 811 := by decide
  have h811Word : (811 : UInt256) = UInt256.ofNat 811 := by decide
  have horNat : (scanOr s.memory count).toNat ≠ 0 := by
    intro hz
    apply hor
    apply Challenge.EvmProof.Word.word_ext
    rw [hz]
    rfl
  simp [scanNonzeroPath, opAt, pushAt, wfOp, scanExit, scanLoop,
    scanNonzero, scanPCs, hrun, hcode, hc2, hc3, hc4, h811, h811Word,
    horNat, jump811, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_scanZero (s : State) (count b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1011) (hm : m < 2 ^ 256)
    (hor : scanOr s.memory count = 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanZeroPath
      (scanExit s count ([UInt256.ofNat b, UInt256.ofNat e,
        UInt256.ofNat m, UInt256.ofNat baseOff, UInt256.ofNat expOff,
        UInt256.ofNat modOff, returnDest] ++ rest)) =
      some (scanZeroFinal s count b e m baseOff expOff modOff returnDest
        rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hzeroNat : (scanOr s.memory count).toNat = 0 := by rw [hor]; decide
  have hmNat : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hm]
  have h6144Nat : (6144 : UInt256).toNat = 6144 := by decide
  have h0Nat : (0 : UInt256).toNat = 0 := by decide
  simp [scanZeroPath, scanNonzeroPath, opAt, pushAt, wfOp, scanExit,
    scanLoop, scanZeroFinal, scanPCs, hrun, hor, hzeroNat, hmNat,
    h6144Nat, h0Nat, hc9, hc10, hc11, hc12, UInt256.isTrue,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def gasSteps_scanSetup (s : State) (count : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scanEntry s count rest)
      (scanLoop s count 0 rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scanSetupPath
      (by simpa [scanEntry, Artifact.referenceArtifact] using hcode)
      (by simpa [scanEntry, State.fork] using hfork)
      (run_scanSetup s count rest hcap hrun)
      (by simpa [scanEntry] using hrun)
      (by simpa [scanEntry, State.fork] using hnp)

def gasSteps_scanIteration (s : State) (count i : Nat)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcount : count ≤ 32) (hi : i < count)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scanLoop s count i rest)
      (scanLoop s count (i + 1) rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scanGuardPath
      (by simpa [scanLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [scanLoop, State.fork] using hfork)
      (run_scanGuard s count i rest hcap (by omega) hi hrun)
      (by simpa [scanLoop] using hrun)
      (by simpa [scanLoop, State.fork] using hnp)).trans
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scanBodyPath
      (by simpa [scanBody, scanLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [scanBody, scanLoop, State.fork] using hfork)
      (run_scanBody s count i rest hcap hcount hi hcode hrun)
      (by simpa [scanBody, scanLoop] using hrun)
      (by simpa [scanBody, scanLoop, State.fork] using hnp))

def gasSteps_scanLoop (s : State) (count : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018) (hcount : count ≤ 32)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scanLoop s count 0 rest)
      (scanLoop s count count rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_scanIteration s count i rest hcap hcount hi hcode hfork hrun hnp

def gasSteps_scanFinishNonzero (s : State) (count : Nat)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcount : count ≤ 32) (hor : scanOr s.memory count ≠ 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scanLoop s count count rest)
      (scanNonzero s count rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scanGuardPath
      (by simpa [scanLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [scanLoop, State.fork] using hfork)
      (run_scanFinishGuard s count rest hcap (by omega) hcode hrun)
      (by simpa [scanLoop] using hrun)
      (by simpa [scanLoop, State.fork] using hnp)).trans
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scanNonzeroPath
      (by simpa [scanExit, scanLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [scanExit, scanLoop, State.fork] using hfork)
      (run_scanNonzero s count rest hcap hor hcode hrun)
      (by simpa [scanExit, scanLoop] using hrun)
      (by simpa [scanExit, scanLoop, State.fork] using hnp))

def gasSteps_scanNonzeroTotal (s : State) (count : Nat)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcount : count ≤ 32) (hor : scanOr s.memory count ≠ 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scanEntry s count rest)
      (scanNonzero s count rest) :=
  (gasSteps_scanSetup s count rest hcap hcode hfork hrun hnp).trans <|
    (gasSteps_scanLoop s count rest hcap hcount hcode hfork hrun hnp).trans <|
      gasSteps_scanFinishNonzero s count rest hcap hcount hor hcode hfork
        hrun hnp

theorem gasSteps_scanIteration_cost_potential (s : State) (count i : Nat)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcount : count ≤ 32) (hi : i < count)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_scanIteration s count i rest hcap hcount hi hcode hfork hrun
        hnp).cost + MachineState.memCost
          (scanLoop s count i rest).activeWords.toNat =
      74 + MachineState.memCost
        (scanLoop s count (i + 1) rest).activeWords.toNat := by
  have hg := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanGuardPath 26 (run_scanGuard s count i rest hcap (by omega) hi hrun)
      (by simpa [scanLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hb := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanBodyPath 48
      (run_scanBody s count i rest hcap hcount hi hcode hrun)
      (by simpa [scanBody, scanLoop, State.fork] using hfork)
      (by decide) (by decide)
  have ht := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka scanGuardPath
        (by simpa [scanLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [scanLoop, State.fork] using hfork)
        (run_scanGuard s count i rest hcap (by omega) hi hrun)
        (by simpa [scanLoop] using hrun)
        (by simpa [scanLoop, State.fork] using hnp))
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka scanBodyPath
        (by simpa [scanBody, scanLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [scanBody, scanLoop, State.fork] using hfork)
        (run_scanBody s count i rest hcap hcount hi hcode hrun)
        (by simpa [scanBody, scanLoop] using hrun)
        (by simpa [scanBody, scanLoop, State.fork] using hnp))
    26 48 hg hb
  simpa [gasSteps_scanIteration] using ht

theorem gasSteps_scanLoop_cost_potential (s : State) (count : Nat)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcount : count ≤ 32)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_scanLoop s count rest hcap hcount hcode hfork hrun hnp).cost +
        MachineState.memCost (scanLoop s count 0 rest).activeWords.toNat =
      count * 74 + MachineState.memCost
        (scanLoop s count count rest).activeWords.toNat := by
  unfold gasSteps_scanLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  exact gasSteps_scanIteration_cost_potential s count i rest hcap hcount hi
    hcode hfork hrun hnp

theorem gasSteps_scanNonzeroTotal_cost_potential (s : State) (count : Nat)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcount : count ≤ 32) (hor : scanOr s.memory count ≠ 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_scanNonzeroTotal s count rest hcap hcount hor hcode hfork hrun
        hnp).cost + MachineState.memCost s.activeWords.toNat =
      (50 + count * 74) + MachineState.memCost
        (scanNonzero s count rest).activeWords.toNat := by
  have hs := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanSetupPath 5 (run_scanSetup s count rest hcap hrun)
      (by simpa [scanEntry, State.fork] using hfork)
      (by decide) (by decide)
  have hl := gasSteps_scanLoop_cost_potential s count rest hcap hcount hcode
    hfork hrun hnp
  have hg := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanGuardPath 26
      (run_scanFinishGuard s count rest hcap (by omega) hcode hrun)
      (by simpa [scanLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hn := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanNonzeroPath 19 (run_scanNonzero s count rest hcap hor hcode hrun)
      (by simpa [scanExit, scanLoop, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_scanNonzeroTotal gasSteps_scanSetup
    gasSteps_scanFinishNonzero
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [scanEntry, scanLoop, scanExit, scanNonzero, scanWords,
    scanOr] at hs hl hg hn ⊢
  omega

def gasSteps_scanZeroTotal (s : State) (count b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1011) (hcount : count ≤ 32)
    (hm : m < 2 ^ 256) (hor : scanOr s.memory count = 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scanEntry s count ([UInt256.ofNat b, UInt256.ofNat e,
        UInt256.ofNat m, UInt256.ofNat baseOff, UInt256.ofNat expOff,
        UInt256.ofNat modOff, returnDest] ++ rest))
      (scanZeroFinal s count b e m baseOff expOff modOff returnDest rest) := by
  let caller := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff, UInt256.ofNat modOff,
    returnDest] ++ rest
  have hcaller : caller.length < 1018 := by simp [caller]; omega
  exact (gasSteps_scanSetup s count caller hcaller hcode hfork hrun hnp).trans <|
    (gasSteps_scanLoop s count caller hcaller hcount hcode hfork hrun hnp).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka scanGuardPath
        (by simpa [scanLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [scanLoop, State.fork] using hfork)
        (run_scanFinishGuard s count caller hcaller (by omega) hcode hrun)
        (by simpa [scanLoop] using hrun)
        (by simpa [scanLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka scanZeroPath
        (by simpa [scanExit, scanLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [scanExit, scanLoop, State.fork] using hfork)
        (run_scanZero s count b e m baseOff expOff modOff returnDest rest
          hcap hm hor hrun)
        (by simpa [scanExit, scanLoop] using hrun)
        (by simpa [scanExit, scanLoop, State.fork] using hnp))

theorem gasSteps_scanZeroTotal_cost_potential (s : State)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcount : count ≤ 32) (hm : m < 2 ^ 256)
    (hor : scanOr s.memory count = 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_scanZeroTotal s count b e m baseOff expOff modOff returnDest
        rest hcap hcount hm hor hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      (56 + count * 74) + MachineState.memCost
        (scanZeroFinal s count b e m baseOff expOff modOff returnDest rest).activeWords.toNat := by
  let caller := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff, UInt256.ofNat modOff,
    returnDest] ++ rest
  have hcaller : caller.length < 1018 := by simp [caller]; omega
  have hs := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanSetupPath 5 (run_scanSetup s count caller hcaller hrun)
      (by simpa [scanEntry, State.fork] using hfork)
      (by decide) (by decide)
  have hl := gasSteps_scanLoop_cost_potential s count caller hcaller hcount
    hcode hfork hrun hnp
  have hg := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanGuardPath 26
      (run_scanFinishGuard s count caller hcaller (by omega) hcode hrun)
      (by simpa [scanLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hz := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    scanZeroPath 25
      (run_scanZero s count b e m baseOff expOff modOff returnDest rest
        hcap hm hor hrun)
      (by simpa [scanExit, scanLoop, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_scanZeroTotal gasSteps_scanSetup
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [caller, scanEntry, scanLoop, scanExit, scanZeroFinal, scanWords,
    scanOr] at hs hl hg hz ⊢
  omega

private theorem natOr_eq_zero_iff (a b : Nat) :
    a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hbit (i : Nat) :
        a.testBit i = false ∧ b.testBit i = false := by
      have := congrArg (fun n => n.testBit i) h
      simpa using this
    constructor
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).1
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).2
  · rintro ⟨rfl, rfl⟩
    decide

private theorem wordOr_eq_zero_iff (a b : UInt256) :
    UInt256.lor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hzeroNat : (0 : UInt256).toNat = 0 := by decide
    have hnat : a.toNat ||| b.toNat = 0 := by
      rw [← Challenge.EvmProof.Word.word_toNat_lor, h]
      rfl
    rcases (natOr_eq_zero_iff a.toNat b.toNat).1 hnat with ⟨ha, hb⟩
    constructor
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact ha
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact hb
  · rintro ⟨rfl, rfl⟩
    decide

theorem scanOr_eq_zero_iff (memory : ByteArray) (count : Nat) :
    scanOr memory count = 0 ↔
      ∀ i, i < count → MachineState.readWord memory (32 * i) = 0 := by
  induction count with
  | zero => simp [scanOr]
  | succ count ih =>
      rw [scanOr, wordOr_eq_zero_iff, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hprev i hi
        · exact hlast
      · intro hall
        exact ⟨fun i hi => hall i (by omega), hall count (by omega)⟩

theorem scanOr_eq_zero_iff_value_eq_zero (memory : ByteArray)
    (count value : Nat) (hrep : Limbs.Represents memory 0 count value) :
    scanOr memory count = 0 ↔ value = 0 := by
  rw [scanOr_eq_zero_iff]
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  constructor
  · intro hall
    rw [← Limbs.value_of_represents hrep]
    have hzero : Limbs.memoryLimbs memory 0 count =
        List.replicate count 0 := by
      apply List.ext_get
      · simp [Limbs.memoryLimbs]
      · intro i hiLeft hiRight
        have hi : i < count := by simpa [Limbs.memoryLimbs] using hiLeft
        have hw := congrArg UInt256.toNat (hall i hi)
        rw [hzeroNat] at hw
        simpa [Limbs.memoryLimbs, Nat.mul_comm] using hw
    rw [hzero]
    simp
  · intro hvalue i hi
    subst value
    have hlimbs : Limbs.memoryLimbs memory 0 count =
        List.replicate count 0 := by
      rw [hrep.2]
      simp [Limbs.limbDigits, Nat.digitsAppend]
    have hget := congrArg (fun xs : List Nat => xs[i]?) hlimbs
    have hwordNat : (MachineState.readWord memory (32 * i)).toNat = 0 := by
      simpa [Limbs.memoryLimbs, Nat.mul_comm, hi] using hget
    apply Challenge.EvmProof.Word.word_ext
    rw [hzeroNat]
    exact hwordNat

end Challenge.Modexp.Reference.Proofs.Bytecode.BigModulus
