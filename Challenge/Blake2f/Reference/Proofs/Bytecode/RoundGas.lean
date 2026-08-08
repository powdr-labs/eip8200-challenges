import Challenge.Blake2f.Reference.Proofs.Bytecode.Round

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-! Exact one-round trace composition and gas certification. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.Round

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

structure AccessSafe (memory : ByteArray) (round : Nat) : Prop where
  row : (MixG.rowOffset (UInt256.ofNat round)).toNat + 32 ≤ 58 * 32
  message : ∀ column, column < 16 →
    (MixG.messageOffset
      (MixG.rowWord memory (UInt256.ofNat round)) (UInt256.ofNat column)).toNat +
        32 ≤ 58 * 32

structure IterationSafe (memory : ByteArray) (round : Nat) : Prop where
  zero : AccessSafe memory round
  one : AccessSafe (memory1 memory round) round
  two : AccessSafe (memory2 memory round) round
  three : AccessSafe (memory3 memory round) round
  four : AccessSafe (memory4 memory round) round
  five : AccessSafe (memory5 memory round) round
  six : AccessSafe (memory6 memory round) round
  seven : AccessSafe (memory7 memory round) round

def memories (initial : ByteArray) : Nat → ByteArray
  | 0 => initial
  | round + 1 => transition (memories initial round) round

private def gasStepsBlock
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps a b := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact hresult
  · exact hrun
  · exact hnp

@[simp] private theorem gasStepsBlock_cost
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    (gasStepsBlock path hresult hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost path a := rfl

private theorem return909 : Decode.isValidJumpDest referenceBytecode 909 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 452 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return934 : Decode.isValidJumpDest referenceBytecode 934 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 463 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return959 : Decode.isValidJumpDest referenceBytecode 959 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 474 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return984 : Decode.isValidJumpDest referenceBytecode 984 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 485 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return1009 : Decode.isValidJumpDest referenceBytecode 1009 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 496 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return1034 : Decode.isValidJumpDest referenceBytecode 1034 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 507 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return1059 : Decode.isValidJumpDest referenceBytecode 1059 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 518 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private theorem return1084 : Decode.isValidJumpDest referenceBytecode 1084 = true := by
  have h := Artifact.referenceArtifact.isValidJumpDest_index 529 (by rfl)
  simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
    Artifact.referenceInstructions] using h

private def mixGasSteps (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (a b c d xColumn yColumn returnDest : Nat)
    (safe : AccessSafe memory round)
    (hxColumn : xColumn < 16) (hyColumn : yColumn < 16)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ha : a + 32 ≤ 58 * 32) (hb : b + 32 ≤ 58 * 32)
    (hc : c + 32 ≤ 58 * 32) (hd : d + 32 ≤ 58 * 32)
    (hreturnLt : returnDest < 2 ^ 256)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest = true) :
    Challenge.EvmProof.GasSteps
      (MixG.entryState (baseState s memory) (UInt256.ofNat a) (UInt256.ofNat b)
        (UInt256.ofNat c) (UInt256.ofNat d) (UInt256.ofNat round)
        (UInt256.ofNat xColumn) (UInt256.ofNat yColumn)
        (UInt256.ofNat returnDest) (tail round rounds flag))
      (MixG.finalState (baseState s memory) (UInt256.ofNat a) (UInt256.ofNat b)
        (UInt256.ofNat c) (UInt256.ofNat d) (UInt256.ofNat round)
        (UInt256.ofNat xColumn) (UInt256.ofNat yColumn)
        (UInt256.ofNat returnDest) (tail round rounds flag)) := by
  apply MixG.gasSteps (baseState s memory) (UInt256.ofNat a) (UInt256.ofNat b)
    (UInt256.ofNat c) (UInt256.ofNat d) (UInt256.ofNat round)
    (UInt256.ofNat xColumn) (UInt256.ofNat yColumn) (UInt256.ofNat returnDest)
    (tail round rounds flag)
  · simp [tail]
  · simpa [baseState] using hrun
  · simpa [baseState] using hcode
  · simpa [baseState, State.fork] using hfork
  · simpa [baseState] using hnp
  · rfl
  · exact safe.row
  · exact safe.message xColumn hxColumn
  · exact safe.message yColumn hyColumn
  · rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    exact ha
  · rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    exact hb
  · rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    exact hc
  · rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    exact hd
  · rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hreturnLt]
    exact hreturn

def iterationGasSteps (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (safe : IterationSafe memory round)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hround : round < rounds.toNat) :
    Challenge.EvmProof.GasSteps (loopState s round rounds flag memory)
      (loopState s (round + 1) rounds flag (transition memory round)) := by
  have gtest := gasStepsBlock testSetupPath
    (run_testSetup s memory round rounds flag hrun hcode hround)
    (by simpa [loopState, baseState] using hcode)
    (by simpa [loopState, baseState, State.fork] using hfork)
    (by simpa [loopState, baseState] using hrun)
    (by simpa [loopState, baseState] using hnp)
  have g1 := mixGasSteps s memory round rounds flag 768 896 1024 1152 0 1 909
    safe.zero (by omega) (by omega) hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return909
  have gsetup2 := gasStepsBlock setup2Path
    (run_setup2 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  have g2 := mixGasSteps s (memory1 memory round) round rounds flag
    800 928 1056 1184 2 3 934 safe.one (by omega) (by omega)
    hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return934
  have gsetup3 := gasStepsBlock setup3Path
    (run_setup3 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  have g3 := mixGasSteps s (memory2 memory round) round rounds flag
    832 960 1088 1216 4 5 959 safe.two (by omega) (by omega)
    hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return959
  have gsetup4 := gasStepsBlock setup4Path
    (run_setup4 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  have g4 := mixGasSteps s (memory3 memory round) round rounds flag
    864 992 1120 1248 6 7 984 safe.three (by omega) (by omega)
    hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return984
  have gsetup5 := gasStepsBlock setup5Path
    (run_setup5 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  have g5 := mixGasSteps s (memory4 memory round) round rounds flag
    768 928 1088 1248 8 9 1009 safe.four (by omega) (by omega)
    hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return1009
  have gsetup6 := gasStepsBlock setup6Path
    (run_setup6 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  have g6 := mixGasSteps s (memory5 memory round) round rounds flag
    800 960 1120 1152 10 11 1034 safe.five (by omega) (by omega)
    hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return1034
  have gsetup7 := gasStepsBlock setup7Path
    (run_setup7 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  have g7 := mixGasSteps s (memory6 memory round) round rounds flag
    832 992 1024 1184 12 13 1059 safe.six (by omega) (by omega)
    hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return1059
  have gsetup8 := gasStepsBlock setup8Path
    (run_setup8 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  have g8 := mixGasSteps s (memory7 memory round) round rounds flag
    864 896 1056 1216 14 15 1084 safe.seven (by omega) (by omega)
    hrun hcode hfork hnp
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat])
    (by norm_num [Challenge.EvmProof.Word.word_toNat_ofNat]) (by norm_num) return1084
  have ginc := gasStepsBlock incrementPath
    (run_increment s memory round rounds flag hrun hcode hround)
    (by simpa [MixG.finalState, baseState] using hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork)
    (by simpa [MixG.finalState, baseState] using hrun)
    (by simpa [MixG.finalState, baseState] using hnp)
  exact gtest.trans (g1.trans (gsetup2.trans (g2.trans
    (gsetup3.trans (g3.trans (gsetup4.trans (g4.trans
      (gsetup5.trans (g5.trans (gsetup6.trans (g6.trans
        (gsetup7.trans (g7.trans (gsetup8.trans (g8.trans ginc)))))))))))))))

private theorem locatedCost_eq
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State} (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hfork : a.fork = .Osaka) (hactive : b.activeWords = a.activeWords)
    (hfree : ∀ located ∈ path,
      Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hwork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path a = work := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hwork
  rw [hactive] at hpotential
  omega

private theorem copyFree_of_all
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (hall : path.all
      (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true) :
    ∀ located ∈ path, Challenge.EvmProof.Meter.CopyFree located.instruction :=
  List.all_eq_true.mp hall

theorem testSetup_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hround : round < rounds.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost testSetupPath
      (loopState s round rounds flag memory) = 59 := by
  apply locatedCost_eq testSetupPath 59
    (run_testSetup s memory round rounds flag hrun hcode hround)
    (by simpa [loopState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all testSetupPath (by decide)
  · decide

theorem setup2_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setup2Path
      (MixG.finalState (baseState s memory)
        (UInt256.ofNat 768) (UInt256.ofNat 896) (UInt256.ofNat 1024)
        (UInt256.ofNat 1152) (UInt256.ofNat round) (UInt256.ofNat 0)
        (UInt256.ofNat 1) (UInt256.ofNat 909)
        (tail round rounds flag)) = 36 := by
  apply locatedCost_eq setup2Path 36
    (run_setup2 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setup2Path (by decide)
  · decide

theorem setup3_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setup3Path
      (MixG.finalState (baseState s (memory1 memory round))
        (UInt256.ofNat 800) (UInt256.ofNat 928) (UInt256.ofNat 1056)
        (UInt256.ofNat 1184) (UInt256.ofNat round) (UInt256.ofNat 2)
        (UInt256.ofNat 3) (UInt256.ofNat 934)
        (tail round rounds flag)) = 36 := by
  apply locatedCost_eq setup3Path 36
    (run_setup3 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setup3Path (by decide)
  · decide

theorem setup4_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setup4Path
      (MixG.finalState (baseState s (memory2 memory round))
        (UInt256.ofNat 832) (UInt256.ofNat 960) (UInt256.ofNat 1088)
        (UInt256.ofNat 1216) (UInt256.ofNat round) (UInt256.ofNat 4)
        (UInt256.ofNat 5) (UInt256.ofNat 959)
        (tail round rounds flag)) = 36 := by
  apply locatedCost_eq setup4Path 36
    (run_setup4 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setup4Path (by decide)
  · decide

theorem setup5_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setup5Path
      (MixG.finalState (baseState s (memory3 memory round))
        (UInt256.ofNat 864) (UInt256.ofNat 992) (UInt256.ofNat 1120)
        (UInt256.ofNat 1248) (UInt256.ofNat round) (UInt256.ofNat 6)
        (UInt256.ofNat 7) (UInt256.ofNat 984)
        (tail round rounds flag)) = 36 := by
  apply locatedCost_eq setup5Path 36
    (run_setup5 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setup5Path (by decide)
  · decide

theorem setup6_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setup6Path
      (MixG.finalState (baseState s (memory4 memory round))
        (UInt256.ofNat 768) (UInt256.ofNat 928) (UInt256.ofNat 1088)
        (UInt256.ofNat 1248) (UInt256.ofNat round) (UInt256.ofNat 8)
        (UInt256.ofNat 9) (UInt256.ofNat 1009)
        (tail round rounds flag)) = 36 := by
  apply locatedCost_eq setup6Path 36
    (run_setup6 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setup6Path (by decide)
  · decide

theorem setup7_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setup7Path
      (MixG.finalState (baseState s (memory5 memory round))
        (UInt256.ofNat 800) (UInt256.ofNat 960) (UInt256.ofNat 1120)
        (UInt256.ofNat 1152) (UInt256.ofNat round) (UInt256.ofNat 10)
        (UInt256.ofNat 11) (UInt256.ofNat 1034)
        (tail round rounds flag)) = 36 := by
  apply locatedCost_eq setup7Path 36
    (run_setup7 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setup7Path (by decide)
  · decide

theorem setup8_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost setup8Path
      (MixG.finalState (baseState s (memory6 memory round))
        (UInt256.ofNat 832) (UInt256.ofNat 992) (UInt256.ofNat 1024)
        (UInt256.ofNat 1184) (UInt256.ofNat round) (UInt256.ofNat 12)
        (UInt256.ofNat 13) (UInt256.ofNat 1059)
        (tail round rounds flag)) = 36 := by
  apply locatedCost_eq setup8Path 36
    (run_setup8 s memory round rounds flag hrun hcode)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all setup8Path (by decide)
  · decide

theorem increment_cost (s : State) (memory : ByteArray) (round : Nat)
    (rounds flag : UInt256) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hround : round < rounds.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost incrementPath
      (MixG.finalState (baseState s (memory7 memory round))
        864 896 1056 1216 (UInt256.ofNat round) 14 15 1084
        (tail round rounds flag)) = 27 := by
  apply locatedCost_eq incrementPath 27
    (run_increment s memory round rounds flag hrun hcode hround)
    (by simpa [MixG.finalState, baseState, State.fork] using hfork) rfl
  · exact copyFree_of_all incrementPath (by decide)
  · decide

@[simp] theorem iterationGasSteps_cost (s : State) (memory : ByteArray)
    (round : Nat) (rounds flag : UInt256) (safe : IterationSafe memory round)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hround : round < rounds.toNat) :
    (iterationGasSteps s memory round rounds flag safe hrun hcode hfork hnp
      hround).cost = 3970 := by
  unfold iterationGasSteps mixGasSteps
  simp only [Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost,
    MixG.gasSteps_cost]
  rw [testSetup_cost s memory round rounds flag hrun hcode hfork hround,
    setup2_cost s memory round rounds flag hrun hcode hfork,
    setup3_cost s memory round rounds flag hrun hcode hfork,
    setup4_cost s memory round rounds flag hrun hcode hfork,
    setup5_cost s memory round rounds flag hrun hcode hfork,
    setup6_cost s memory round rounds flag hrun hcode hfork,
    setup7_cost s memory round rounds flag hrun hcode hfork,
    setup8_cost s memory round rounds flag hrun hcode hfork,
    increment_cost s memory round rounds flag hrun hcode hfork hround]

def loopGasSteps (s : State) (initial : ByteArray) (rounds flag : UInt256)
    (safe : ∀ round, round < rounds.toNat →
      IterationSafe (memories initial round) round)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s 0 rounds flag initial)
      (loopState s rounds.toNat rounds flag (memories initial rounds.toNat)) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (count := rounds.toNat)
    (I := fun round => loopState s round rounds flag (memories initial round))
    (fun round hround => iterationGasSteps s (memories initial round) round
      rounds flag (safe round hround) hrun hcode hfork hnp hround)

@[simp] theorem loopGasSteps_cost (s : State) (initial : ByteArray)
    (rounds flag : UInt256)
    (safe : ∀ round, round < rounds.toNat →
      IterationSafe (memories initial round) round)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (loopGasSteps s initial rounds flag safe hrun hcode hfork hnp).cost =
      3970 * rounds.toNat := by
  unfold loopGasSteps
  simpa [Nat.mul_comm] using
    (Challenge.EvmProof.GasSteps.iterateBounded_cost_of_const
    rounds.toNat 3970
    (fun round hround => iterationGasSteps s (memories initial round) round
      rounds flag (safe round hround) hrun hcode hfork hnp hround)
    (fun round hround => iterationGasSteps_cost s (memories initial round) round
      rounds flag (safe round hround) hrun hcode hfork hnp hround))

end Challenge.Blake2f.Reference.Proofs.Bytecode.Round
