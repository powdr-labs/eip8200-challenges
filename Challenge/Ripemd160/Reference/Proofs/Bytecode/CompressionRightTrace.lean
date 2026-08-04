import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Direct trace of the RIPEMD-160 right line and compression tail

This module completes the half of `compress` deliberately left as a stable
seam by `CompressionTrace`: the 80 right-line rounds and the final cross-line
combination.  All instruction blocks are the artifact-pinned `Located` paths
from that module; calls to `tableAt` and `round` reuse their independent
traces.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRightTrace

open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace

@[simp] private theorem rightInitPC :
    Artifact.referenceArtifact.instructionPC 516 = 728 := by rfl

@[simp] private theorem rightTestPC (j : Nat) (hlo : 517 ≤ j) (hhi : j ≤ 523) :
    Artifact.referenceArtifact.instructionPC j =
      [729, 730, 732, 733, 734, 735, 738][j - 517]! := by
  interval_cases j <;> rfl

@[simp] private theorem rightPrefixPC (j : Nat) (hlo : 524 ≤ j)
    (hhi : j ≤ 539) :
    Artifact.referenceArtifact.instructionPC j =
      [739, 740, 742, 743, 746, 747, 749, 750, 753, 754, 755, 758,
       759, 760, 763, 766][j - 524]! := by
  interval_cases j <;> rfl

@[simp] private theorem rightMiddlePC (j : Nat) (hlo : 540 ≤ j)
    (hhi : j ≤ 546) :
    Artifact.referenceArtifact.instructionPC j =
      [767, 768, 771, 772, 773, 776, 779][j - 540]! := by
  interval_cases j <;> rfl

@[simp] private theorem rightSuffixPC (j : Nat) (hlo : 547 ≤ j)
    (hhi : j ≤ 553) :
    Artifact.referenceArtifact.instructionPC j =
      [780, 781, 782, 784, 785, 788, 791][j - 547]! := by
  interval_cases j <;> rfl

@[simp] private theorem rightIncrementPC (j : Nat) (hlo : 554 ≤ j)
    (hhi : j ≤ 562) :
    Artifact.referenceArtifact.instructionPC j =
      [792, 793, 794, 796, 797, 798, 799, 800, 803][j - 554]! := by
  interval_cases j <;> rfl

@[simp] private theorem rightExitPC (j : Nat) (hlo : 563 ≤ j) (hhi : j ≤ 564) :
    Artifact.referenceArtifact.instructionPC j = [804, 805][j - 563]! := by
  interval_cases j <;> rfl

def rightRoundIndex (i : Nat) : Nat := 4 - roundIndex i

def rightFirstReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  TableTrace.tableAtReturned (afterConstantLoad s 1728 i)
    (UInt256.ofNat 1472) (UInt256.ofNat i)
    (UInt256.ofNat 767)
    ([constantAt s 1728 i, UInt256.ofNat 792, UInt256.ofNat (roundIndex i),
      UInt256.ofNat i, messageOffset, returnDest] ++ rest)

def rightSecondReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let q := rightFirstReturned s messageOffset returnDest rest i
  TableTrace.tableAtReturned q (UInt256.ofNat 1280) (UInt256.ofNat i)
    (UInt256.ofNat 780)
    ([TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i),
      constantAt s 1728 i, UInt256.ofNat 792,
      UInt256.ofNat (roundIndex i), UInt256.ofNat i,
      messageOffset, returnDest] ++ rest)

def rightRoundState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let q1 := rightFirstReturned s messageOffset returnDest rest i
  let q := rightSecondReturned s messageOffset returnDest rest i
  RoundTrace.roundReturned q (UInt256.ofNat 352) (rightRoundIndex i)
    (TableTrace.tableValue q1 (UInt256.ofNat 1280) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
    (constantAt s 1728 i) (UInt256.ofNat 792)
    (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
      messageOffset :: returnDest :: rest)

def rightInitEntry (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 728
           stack := [messageOffset, returnDest] ++ rest }

set_option linter.unusedSimpArgs false in
theorem run_rightInit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightInitLocated
      (rightInitEntry s messageOffset returnDest rest) =
        some (rightLoopAt s messageOffset returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [rightInitLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rightInitEntry, rightLoopAt, hrun, hc2]

def gasSteps_rightInit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightInitEntry s messageOffset returnDest rest)
      (rightLoopAt s messageOffset returnDest rest 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightInitLocated
      (s := rightInitEntry s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_rightInit s messageOffset returnDest rest hstack hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_rightRoundPrefix (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightRoundPrefixLocated
      (rightBodyAt s messageOffset returnDest rest i) =
      some (TableTrace.tableAtEntry (afterConstantLoad s 1728 i)
        (UInt256.ofNat 1472) (UInt256.ofNat i)
        (UInt256.ofNat 767)
        ([constantAt s 1728 i, UInt256.ofNat 792,
          UInt256.ofNat (roundIndex i), UInt256.ofNat i,
          messageOffset, returnDest] ++ rest)) := by
  have hshift : UInt256.shiftRight (UInt256.ofNat i) (UInt256.ofNat 4) =
      UInt256.ofNat (roundIndex i) := by
    rw [roundIndex, Challenge.EvmProof.Word.shiftRight_ofNat (by omega)
      (by decide)]
    simp [Nat.shiftRight_eq_div_pow]
  have haddr : UInt256.ofNat 1728 +
      UInt256.shiftLeft (UInt256.ofNat (roundIndex i)) (UInt256.ofNat 5) =
      UInt256.ofNat (1728 + roundIndex i * 32) := by
    have hj : roundIndex i < 5 := by unfold roundIndex; omega
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
  have haddrNat : (UInt256.ofNat 1728 +
      UInt256.shiftLeft (UInt256.ofNat (roundIndex i)) (UInt256.ofNat 5)).toNat =
      1728 + roundIndex i * 32 := by
    rw [haddr, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold roundIndex; omega)]
  have hsmall : 1728 + roundIndex i * 32 < 2 ^ 256 := by
    unfold roundIndex
    omega
  have hmod : (1728 + roundIndex i * 32) % 2 ^ 256 =
      1728 + roundIndex i * 32 := Nat.mod_eq_of_lt hsmall
  have hmodSize : (1728 + roundIndex i * 32) % UInt256.size =
      1728 + roundIndex i * 32 := by
    apply Nat.mod_eq_of_lt
    change 1728 + roundIndex i * 32 < 2 ^ 256
    exact hsmall
  have hmodLiteral : (1728 + roundIndex i * 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      1728 + roundIndex i * 32 := by
    apply Nat.mod_eq_of_lt
    change 1728 + roundIndex i * 32 < 2 ^ 256
    exact hsmall
  have hdest : Decode.isValidJumpDest referenceBytecode 120 = true := by decide
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 })
    [rightRoundPrefixLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rightBodyAt, TableTrace.tableAtEntry, constantAt, afterConstantLoad,
      State.activeWordsAfterUInt256, hrun, hcode, hshift,
      haddr, haddrNat, hsmall, hmod, hmodSize, hmodLiteral,
      hdest, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_rightRoundMiddle (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightRoundMiddleLocated
      (rightFirstReturned s messageOffset returnDest rest i) =
      some (TableTrace.tableAtEntry
        (rightFirstReturned s messageOffset returnDest rest i)
        (UInt256.ofNat 1280) (UInt256.ofNat i) (UInt256.ofNat 780)
        ([TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i),
          constantAt s 1728 i, UInt256.ofNat 792,
          UInt256.ofNat (roundIndex i), UInt256.ofNat i,
          messageOffset, returnDest] ++ rest)) := by
  have hdest : Decode.isValidJumpDest referenceBytecode 120 = true := by decide
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 200000 })
    [rightRoundMiddleLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rightFirstReturned, TableTrace.tableAtReturned, TableTrace.tableAtEntry,
      TableTrace.tableValue, afterConstantLoad, hrun, hcode, hdest, hcap,
      Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_rightRoundSuffix (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightRoundSuffixLocated
      (rightSecondReturned s messageOffset returnDest rest i) =
      some (RoundTrace.roundEntry
        (rightSecondReturned s messageOffset returnDest rest i)
        (UInt256.ofNat 352) (rightRoundIndex i)
        (TableTrace.tableValue
          (rightFirstReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 1280) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
        (constantAt s 1728 i) (UInt256.ofNat 792)
        (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
          messageOffset :: returnDest :: rest)) := by
  have hj : roundIndex i ≤ 4 := by unfold roundIndex; omega
  have hsub : UInt256.ofNat 4 - UInt256.ofNat (roundIndex i) =
      UInt256.ofNat (rightRoundIndex i) := by
    unfold rightRoundIndex
    exact Challenge.EvmProof.Word.ofNat_sub_ofNat hj (by norm_num)
  have hdest : Decode.isValidJumpDest referenceBytecode 276 = true := by decide
  have hcap (m : Nat) (hm : m ≤ 13) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 200000 })
    [rightRoundSuffixLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rightSecondReturned, rightFirstReturned, RoundTrace.roundEntry,
      TableTrace.tableAtReturned, TableTrace.tableValue, afterConstantLoad,
      hrun, hcode, hsub, hdest, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]


end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRightTrace
