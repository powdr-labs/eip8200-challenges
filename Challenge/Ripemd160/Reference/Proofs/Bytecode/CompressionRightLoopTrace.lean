import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRightTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Direct right-line loop composition

This cached layer composes the certified right-round setup with loop control
and the literal 80-iteration bound.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRightTrace

open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace

def gasSteps_rightRoundSetup (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightBodyAt s messageOffset returnDest rest i)
      (rightRoundState s messageOffset returnDest rest i) := by
  let q0 := afterConstantLoad s 1728 i
  let tail1 := [constantAt s 1728 i, UInt256.ofNat 792,
    UInt256.ofNat (roundIndex i), UInt256.ofNat i,
    messageOffset, returnDest] ++ rest
  let q1 := rightFirstReturned s messageOffset returnDest rest i
  let tail2 := [TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i),
    constantAt s 1728 i, UInt256.ofNat 792, UInt256.ofNat (roundIndex i),
    UInt256.ofNat i, messageOffset, returnDest] ++ rest
  let q2 := rightSecondReturned s messageOffset returnDest rest i
  let roundTail := UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
    messageOffset :: returnDest :: rest
  have hq0code : q0.executionEnv.code = referenceBytecode := by
    simpa [q0, afterConstantLoad] using hcode
  have hq0fork : q0.fork = .Osaka := by
    simpa [q0, afterConstantLoad, State.fork] using hfork
  have hq0run : q0.halt = .Running := by
    simpa [q0, afterConstantLoad] using hrun
  have hq0np : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by
    simpa [q0, afterConstantLoad] using hnp
  have gp := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightRoundPrefixLocated
      (s := rightBodyAt s messageOffset returnDest rest i)
      hcode hfork
      (run_rightRoundPrefix s messageOffset returnDest rest i hi (by omega)
        hcode hrun) hrun hnp
  have gt1 := TableTrace.gasSteps_tableAt q0 (UInt256.ofNat 1472)
    (UInt256.ofNat i) (UInt256.ofNat 767) tail1 (by simp [tail1]; omega)
    hq0code hq0fork hq0run hq0np (by decide)
  have hq1code : q1.executionEnv.code = referenceBytecode := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hcode
  have hq1fork : q1.fork = .Osaka := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad, State.fork] using hfork
  have hq1run : q1.halt = .Running := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hrun
  have hq1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hnp
  have gm := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightRoundMiddleLocated
      (s := q1) hq1code hq1fork
      (run_rightRoundMiddle s messageOffset returnDest rest i (by omega)
        hcode hrun) hq1run hq1np
  have gt2 := TableTrace.gasSteps_tableAt q1 (UInt256.ofNat 1280)
    (UInt256.ofNat i) (UInt256.ofNat 780) tail2 (by simp [tail2]; omega)
    hq1code hq1fork hq1run hq1np (by decide)
  have hq2code : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hcode
  have hq2fork : q2.fork = .Osaka := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad, State.fork] using hfork
  have hq2run : q2.halt = .Running := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hrun
  have hq2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hnp
  have gs := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightRoundSuffixLocated
      (s := q2) hq2code hq2fork
      (run_rightRoundSuffix s messageOffset returnDest rest i hi (by omega)
        hcode hrun) hq2run hq2np
  have gr := RoundTrace.gasSteps_round q2 (UInt256.ofNat 352)
    (rightRoundIndex i) (by unfold rightRoundIndex roundIndex; omega)
    (TableTrace.tableValue q1 (UInt256.ofNat 1280) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
    (constantAt s 1728 i) (UInt256.ofNat 792) roundTail
    (by simp [roundTail]; omega) hq2code hq2fork hq2run hq2np (by decide)
  have hp' : Challenge.EvmProof.GasSteps
      (rightBodyAt s messageOffset returnDest rest i)
      (TableTrace.tableAtEntry q0 (UInt256.ofNat 1472) (UInt256.ofNat i)
        (UInt256.ofNat 767) tail1) :=
    Challenge.EvmProof.GasSteps.cast gp rfl (by simp [q0, tail1])
  have ht1' : Challenge.EvmProof.GasSteps
      (TableTrace.tableAtEntry q0 (UInt256.ofNat 1472) (UInt256.ofNat i)
        (UInt256.ofNat 767) tail1) q1 :=
    Challenge.EvmProof.GasSteps.cast gt1 rfl (by
      simp [q1, q0, tail1, rightFirstReturned])
  have hm' : Challenge.EvmProof.GasSteps q1
      (TableTrace.tableAtEntry q1 (UInt256.ofNat 1280) (UInt256.ofNat i)
        (UInt256.ofNat 780) tail2) :=
    Challenge.EvmProof.GasSteps.cast gm rfl (by simp [q1, tail2])
  have ht2' : Challenge.EvmProof.GasSteps
      (TableTrace.tableAtEntry q1 (UInt256.ofNat 1280) (UInt256.ofNat i)
        (UInt256.ofNat 780) tail2) q2 :=
    Challenge.EvmProof.GasSteps.cast gt2 rfl (by
      simp [q2, q1, tail2, rightSecondReturned])
  have hs' : Challenge.EvmProof.GasSteps q2
      (RoundTrace.roundEntry q2 (UInt256.ofNat 352) (rightRoundIndex i)
        (TableTrace.tableValue q1 (UInt256.ofNat 1280) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
        (constantAt s 1728 i) (UInt256.ofNat 792) roundTail) :=
    Challenge.EvmProof.GasSteps.cast gs rfl (by simp [q2, q1, roundTail])
  have gr' : Challenge.EvmProof.GasSteps
      (RoundTrace.roundEntry q2 (UInt256.ofNat 352) (rightRoundIndex i)
        (TableTrace.tableValue q1 (UInt256.ofNat 1280) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
        (constantAt s 1728 i) (UInt256.ofNat 792) roundTail)
      (rightRoundState s messageOffset returnDest rest i) :=
    Challenge.EvmProof.GasSteps.cast gr rfl (by
      simp [rightRoundState, q2, q1, roundTail])
  exact hp'.trans (ht1'.trans (hm'.trans (ht2'.trans (hs'.trans gr'))))

set_option linter.unusedSimpArgs false in
theorem run_rightTest_continue (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightTestLocated
      (rightLoopAt s messageOffset returnDest rest i) =
        some (rightBodyAt s messageOffset returnDest rest i) := by
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 80) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [rightTestLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rightLoopAt, rightBodyAt, hrun, hlt, hzero, hfalse,
    hc3, hc4, hc5]

def gasSteps_rightTest_continue (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightLoopAt s messageOffset returnDest rest i)
      (rightBodyAt s messageOffset returnDest rest i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightTestLocated
      (s := rightLoopAt s messageOffset returnDest rest i)
  · exact hcode
  · exact hfork
  · exact run_rightTest_continue s messageOffset returnDest rest i hi hstack hrun
  · exact hrun
  · exact hnp

def rightExitTested (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 804
           stack := UInt256.ofNat 80 :: messageOffset :: returnDest :: rest }

def combinationEntry (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 806
           stack := [messageOffset, returnDest] ++ rest }

set_option linter.unusedSimpArgs false in
theorem run_rightTest_exit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightTestLocated
      (rightLoopAt s messageOffset returnDest rest 80) =
        some (rightExitTested s messageOffset returnDest rest) := by
  have hlt : UInt256.lt (UInt256.ofNat 80) (UInt256.ofNat 80) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = 1 := by decide
  have htrue : UInt256.isTrue (1 : UInt256) = true := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 804 = true := by decide
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [rightTestLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rightLoopAt, rightExitTested, hrun, hcode, hlt, hzero, htrue, hdest,
    hc3, hc4, hc5]

def gasSteps_rightTest_exit (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightLoopAt s messageOffset returnDest rest 80)
      (rightExitTested s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightTestLocated
      (s := rightLoopAt s messageOffset returnDest rest 80)
  · exact hcode
  · exact hfork
  · exact run_rightTest_exit s messageOffset returnDest rest hstack hcode hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_rightExit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightExitLocated
      (rightExitTested s messageOffset returnDest rest) =
        some (combinationEntry s messageOffset returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [rightExitLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rightExitTested, combinationEntry, hrun, hc3]

def gasSteps_rightExit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightExitTested s messageOffset returnDest rest)
      (combinationEntry s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightExitLocated
      (s := rightExitTested s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_rightExit s messageOffset returnDest rest hstack hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_rightIncrement (s : State)
    (messageOffset returnDest discard : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightIncrementLocated
      (rightRoundReturned s messageOffset returnDest discard rest i) =
        some (rightLoopAt s messageOffset returnDest rest (i + 1)) := by
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 729 = true := by decide
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [rightIncrementLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rightRoundReturned, rightLoopAt, hrun, hcode, hadd, hdest,
    hc3, hc4, hc5, List.exchange]

def gasSteps_rightIncrement (s : State)
    (messageOffset returnDest discard : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightRoundReturned s messageOffset returnDest discard rest i)
      (rightLoopAt s messageOffset returnDest rest (i + 1)) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightIncrementLocated
      (s := rightRoundReturned s messageOffset returnDest discard rest i)
  · exact hcode
  · exact hfork
  · exact run_rightIncrement s messageOffset returnDest discard rest i hi
      hstack hcode hrun
  · exact hrun
  · exact hnp

@[simp] theorem rightRoundState_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (rightRoundState s messageOffset returnDest rest i).executionEnv =
      s.executionEnv := by rfl

@[simp] theorem rightRoundState_fork (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (rightRoundState s messageOffset returnDest rest i).fork = s.fork := by
  rw [State.fork, rightRoundState_executionEnv]

@[simp] theorem rightRoundState_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (rightRoundState s messageOffset returnDest rest i).halt = s.halt := by rfl

@[simp] theorem rightRoundState_codeAddr (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (rightRoundState s messageOffset returnDest rest i).executionEnv.codeAddr =
      s.executionEnv.codeAddr := by
  rw [rightRoundState_executionEnv]

private theorem rightRoundState_atReturn (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    rightRoundState s messageOffset returnDest rest i =
      rightRoundReturned (rightRoundState s messageOffset returnDest rest i)
        messageOffset returnDest (UInt256.ofNat (roundIndex i)) rest i := by
  rfl

/-- One complete concrete right-line iteration. -/
def gasSteps_rightIterationConcrete (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightLoopAt s messageOffset returnDest rest i)
      (rightLoopAt (rightRoundState s messageOffset returnDest rest i)
        messageOffset returnDest rest (i + 1)) := by
  have gt := gasSteps_rightTest_continue s messageOffset returnDest rest i hi
    (by omega) hcode hfork hrun hnp
  have gr := gasSteps_rightRoundSetup s messageOffset returnDest rest i hi
    hstack hcode hfork hrun hnp
  let q := rightRoundState s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by
    simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gi := gasSteps_rightIncrement q messageOffset returnDest
    (UInt256.ofNat (roundIndex i)) rest i hi (by omega)
    hqcode hqfork hqrun hqnp
  have gr' : Challenge.EvmProof.GasSteps
      (rightBodyAt s messageOffset returnDest rest i)
      (rightRoundReturned q messageOffset returnDest
        (UInt256.ofNat (roundIndex i)) rest i) :=
    Challenge.EvmProof.GasSteps.cast gr rfl (by
      simpa [q] using rightRoundState_atReturn s messageOffset returnDest rest i)
  exact gt.trans (gr'.trans gi)

def rightStates (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => s
  | i + 1 => rightRoundState (rightStates s messageOffset returnDest rest i)
      messageOffset returnDest rest i

@[simp] theorem rightStates_zero (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    rightStates s messageOffset returnDest rest 0 = s := rfl

@[simp] theorem rightStates_succ (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    rightStates s messageOffset returnDest rest (i + 1) =
      rightRoundState (rightStates s messageOffset returnDest rest i)
        messageOffset returnDest rest i := rfl

theorem rightStates_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (rightStates s messageOffset returnDest rest i).executionEnv =
      s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [rightStates, ih]

theorem rightStates_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (rightStates s messageOffset returnDest rest i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [rightStates, ih]

/-- Concrete composition of all 80 right-line rounds. -/
def gasSteps_right80Concrete (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rightLoopAt s messageOffset returnDest rest 0)
      (rightLoopAt (rightStates s messageOffset returnDest rest 80)
        messageOffset returnDest rest 80) := by
  apply gasSteps_right80 (fun i =>
    rightLoopAt (rightStates s messageOffset returnDest rest i)
      messageOffset returnDest rest i)
  intro i hi
  let q := rightStates s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by
    rw [rightStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, rightStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by
    rw [rightStates_halt]
    exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, rightStates_executionEnv] using hnp
  simpa [q, rightStates] using
    gasSteps_rightIterationConcrete q messageOffset returnDest rest i hi hstack
      hqcode hqfork hqrun hqnp


end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRightTrace
