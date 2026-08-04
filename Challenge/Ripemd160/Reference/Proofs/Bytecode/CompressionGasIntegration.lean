import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRoundCostTrace
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionGasIntegration

open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace
open CompressionCostTrace
open CompressionRoundCostTrace

open private concreteScheduleLoop from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCostTrace

private theorem potential_trans
    (cost₁ work₁ cost₂ work₂ p₀ p₁ p₂ : Nat)
    (h₁ : cost₁ + p₀ = work₁ + p₁)
    (h₂ : cost₂ + p₁ = work₂ + p₂) :
    (cost₁ + cost₂) + p₀ = (work₁ + work₂) + p₂ := by
  omega

theorem schedule_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Schedule.gasSteps_schedule s msgOff returnDest rest hstack hcode hfork
      hrun hnp hreturn).cost + MachineState.memCost s.activeWords.toNat =
      scheduleWork + MachineState.memCost
        (Schedule.loopState s msgOff returnDest rest 16).activeWords.toNat := by
  let read : ∀ (i : Nat), i < 16 → GasSteps
      (Schedule.readEntry (Schedule.loopState s msgOff returnDest rest i)
        msgOff returnDest rest i)
      (Schedule.afterRead (Schedule.loopState s msgOff returnDest rest i)
        msgOff returnDest rest i) := fun i hi => by
    let qi := Schedule.loopState s msgOff returnDest rest i
    have hqicode : qi.executionEnv.code = referenceBytecode := by
      simpa [qi] using hcode
    have hqifork : qi.fork = .Osaka := by
      simpa [qi, State.fork] using hfork
    have hqirun : qi.halt = .Running := by simpa [qi] using hrun
    have hqinp : Precompile.isPrecompile qi.executionEnv.fork
        qi.executionEnv.codeAddr = false := by simpa [qi] using hnp
    simpa [qi] using Schedule.gasSteps_readLE qi msgOff returnDest rest i
      hstack hqicode hqifork hqirun hqinp
  change (Schedule.gasSteps_schedule_of_readLE s msgOff returnDest rest hstack
    hcode hfork hrun hnp hreturn read).cost +
      MachineState.memCost s.activeWords.toNat =
    scheduleWork + MachineState.memCost
      (Schedule.loopState s msgOff returnDest rest 16).activeWords.toNat
  let q := Schedule.loopState s msgOff returnDest rest 16
  have hqcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have h0 := blockCost_potential Schedule.scheduleStartPath
    (Schedule.scheduleEntry s msgOff returnDest rest)
    (Schedule.loopState s msgOff returnDest rest 0)
    (Schedule.run_scheduleStart s msgOff returnDest rest (by omega) hrun)
    (by simpa [Schedule.scheduleEntry] using hfork)
    (by simp [Schedule.scheduleStartPath, CopyFree])
  have h1 : (Schedule.gasSteps_loop_of_readLE s msgOff returnDest rest hstack
      hcode hfork hrun hnp read).cost +
        MachineState.memCost s.activeWords.toNat =
      16 * scheduleIterationWork + MachineState.memCost
        (Schedule.loopState s msgOff returnDest rest 16).activeWords.toNat := by
    unfold Schedule.gasSteps_loop_of_readLE
    apply Meter.iterateBounded_cost_potential_add
    intro i hi
    let qi := Schedule.loopState s msgOff returnDest rest i
    have hqicode : qi.executionEnv.code = referenceBytecode := by
      simpa [qi] using hcode
    have hqifork : qi.fork = .Osaka := by
      simpa [qi, State.fork] using hfork
    have hqirun : qi.halt = .Running := by simpa [qi] using hrun
    have hqinp : Precompile.isPrecompile qi.executionEnv.fork
        qi.executionEnv.codeAddr = false := by simpa [qi] using hnp
    have hi := scheduleIteration_cost_potential qi msgOff returnDest rest i hi
      hstack hqicode hqifork hqirun hqinp
    simpa [qi, read, GasSteps.cast_cost, Schedule.loopState] using hi
  have h2 := blockCost_potential Schedule.conditionPath q
    (Schedule.afterExitCondition q msgOff returnDest rest)
    (by simpa [q] using (Schedule.run_condition_exit q msgOff returnDest rest
      (by omega) hqcode hqrun))
    (by simpa [q] using hqfork)
    (by simp [Schedule.conditionPath, CopyFree])
  have h3 := blockCost_potential Schedule.exitPath
    (Schedule.afterExitCondition q msgOff returnDest rest)
    (Schedule.scheduleReturned q returnDest rest)
    (Schedule.run_exit q msgOff returnDest rest (by omega) hqcode hqrun hreturn)
    (by simpa [Schedule.afterExitCondition] using hqfork)
    (by simp [Schedule.exitPath, CopyFree])
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have h012 := potential_trans _ _ _ _ _ _ _ h01 h2
  have hall := potential_trans _ _ _ _ _ _ _ h012 h3
  simpa [Schedule.gasSteps_schedule_of_readLE,
    Schedule.gasSteps_scheduleStart, scheduleWork, q, GasSteps.cast_cost,
    GasSteps.trans_cost, Schedule.scheduleEntry, Schedule.scheduleReturned,
    Nat.add_assoc] using hall

def leftRoundSetupWork (i : Nat) : Nat :=
  Meter.runLocatedBlockStaticCost leftRoundPrefixLocated + tableAtWork +
  Meter.runLocatedBlockStaticCost leftRoundMiddleLocated + tableAtWork +
  Meter.runLocatedBlockStaticCost leftRoundSuffixLocated + roundWork (roundIndex i)

def leftIterationWork (i : Nat) : Nat :=
  Meter.runLocatedBlockStaticCost leftTestLocated + leftRoundSetupWork i +
    Meter.runLocatedBlockStaticCost leftIncrementLocated

theorem leftRoundSetup_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_leftRoundSetup s messageOffset returnDest rest i hi hstack
      hcode hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      leftRoundSetupWork i + MachineState.memCost
        (leftRoundState s messageOffset returnDest rest i).activeWords.toNat := by
  let q0 := afterConstantLoad s 1568 i
  let tail1 := [constantAt s 1568 i, UInt256.ofNat 714,
    UInt256.ofNat (roundIndex i), UInt256.ofNat i,
    messageOffset, returnDest] ++ rest
  let q1 := leftFirstReturned s messageOffset returnDest rest i
  let tail2 := [TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i),
    constantAt s 1568 i, UInt256.ofNat 714, UInt256.ofNat (roundIndex i),
    UInt256.ofNat i, messageOffset, returnDest] ++ rest
  let q2 := leftSecondReturned s messageOffset returnDest rest i
  let roundTail := UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
    messageOffset :: returnDest :: rest
  have hq0code : q0.executionEnv.code = referenceBytecode := by
    simpa [q0, afterConstantLoad] using hcode
  have hq0fork : q0.fork = .Osaka := by
    simpa [q0, afterConstantLoad, State.fork] using hfork
  have hq0run : q0.halt = .Running := by simpa [q0, afterConstantLoad] using hrun
  have hq0np : Precompile.isPrecompile q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by simpa [q0, afterConstantLoad] using hnp
  have h0 := blockCost_potential leftRoundPrefixLocated
    (leftBodyAt s messageOffset returnDest rest i)
    (TableTrace.tableAtEntry q0 (UInt256.ofNat 1376) (UInt256.ofNat i)
      (UInt256.ofNat 693) tail1)
    (run_leftRoundPrefix s messageOffset returnDest rest i hi (by omega)
      hcode hrun)
    (by simpa [leftBodyAt] using hfork)
    (by simp [leftRoundPrefixLocated, CopyFree])
  have h1 := tableAt_cost_potential q0 (UInt256.ofNat 1376)
    (UInt256.ofNat i) (UInt256.ofNat 693) tail1
    (by simp [tail1]; omega) hq0code hq0fork hq0run hq0np (by decide)
  have hq1code : q1.executionEnv.code = referenceBytecode := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hcode
  have hq1fork : q1.fork = .Osaka := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad, State.fork] using hfork
  have hq1run : q1.halt = .Running := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hrun
  have hq1np : Precompile.isPrecompile q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hnp
  have h2 := blockCost_potential leftRoundMiddleLocated q1
    (TableTrace.tableAtEntry q1 (UInt256.ofNat 1184) (UInt256.ofNat i)
      (UInt256.ofNat 706) tail2)
    (run_leftRoundMiddle s messageOffset returnDest rest i (by omega) hcode hrun)
    (by simpa [q1] using hq1fork)
    (by simp [leftRoundMiddleLocated, CopyFree])
  have h3 := tableAt_cost_potential q1 (UInt256.ofNat 1184)
    (UInt256.ofNat i) (UInt256.ofNat 706) tail2
    (by simp [tail2]; omega) hq1code hq1fork hq1run hq1np (by decide)
  have hq2code : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hcode
  have hq2fork : q2.fork = .Osaka := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad, State.fork] using hfork
  have hq2run : q2.halt = .Running := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hrun
  have hq2np : Precompile.isPrecompile q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hnp
  have h4 := blockCost_potential leftRoundSuffixLocated q2
    (RoundTrace.roundEntry q2 (UInt256.ofNat 192) (roundIndex i)
      (TableTrace.tableValue q1 (UInt256.ofNat 1184) (UInt256.ofNat i))
      (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
      (constantAt s 1568 i) (UInt256.ofNat 714) roundTail)
    (run_leftRoundSuffix s messageOffset returnDest rest i (by omega) hcode hrun)
    (by simpa [q2] using hq2fork)
    (by simp [leftRoundSuffixLocated, CopyFree])
  have h5 := round_cost_potential q2 (UInt256.ofNat 192) (roundIndex i)
    (by unfold roundIndex; omega)
    (TableTrace.tableValue q1 (UInt256.ofNat 1184) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
    (constantAt s 1568 i) (UInt256.ofNat 714) roundTail
    (by simp [roundTail]; omega) hq2code hq2fork hq2run hq2np (by decide)
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have h012 := potential_trans _ _ _ _ _ _ _ h01 h2
  have h0123 := potential_trans _ _ _ _ _ _ _ h012 h3
  have h01234 := potential_trans _ _ _ _ _ _ _ h0123 h4
  have hall := potential_trans _ _ _ _ _ _ _ h01234 h5
  simpa [gasSteps_leftRoundSetup, leftRoundSetupWork, leftRoundState,
    leftBodyAt, q0, q1, q2, tail1, tail2, roundTail, GasSteps.trans_cost,
    GasSteps.cast_cost, Nat.add_assoc] using hall

theorem leftIteration_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_leftIterationConcrete s messageOffset returnDest rest i hi hstack
      hcode hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      leftIterationWork i + MachineState.memCost
        (leftRoundState s messageOffset returnDest rest i).activeWords.toNat := by
  let q := leftRoundState s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have h0 := blockCost_potential leftTestLocated
    (leftLoopAt s messageOffset returnDest rest i)
    (leftBodyAt s messageOffset returnDest rest i)
    (run_leftTest_continue s messageOffset returnDest rest i hi (by omega) hrun)
    (by simpa [leftLoopAt] using hfork)
    (by simp [leftTestLocated, CopyFree])
  have h1 := leftRoundSetup_cost_potential s messageOffset returnDest rest i hi
    hstack hcode hfork hrun hnp
  have h2 := blockCost_potential leftIncrementLocated
    (leftRoundReturned q messageOffset returnDest (UInt256.ofNat (roundIndex i))
      rest i)
    (leftLoopAt q messageOffset returnDest rest (i + 1))
    (run_leftIncrement q messageOffset returnDest
      (UInt256.ofNat (roundIndex i)) rest i hi (by omega) hqcode hqrun)
    (by simpa [leftRoundReturned] using hqfork)
    (by simp [leftIncrementLocated, CopyFree])
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have hall := potential_trans _ _ _ _ _ _ _ h01 h2
  simpa [gasSteps_leftIterationConcrete, gasSteps_leftIteration,
    gasSteps_leftTest_continue, gasSteps_leftIncrement,
    leftIterationWork, q, GasSteps.cast_cost, GasSteps.trans_cost,
    leftLoopAt, leftBodyAt, leftRoundState, Nat.add_assoc] using hall

theorem iterateBounded_cost_potential_sum {I : Nat → State}
    (count : Nat) (work : Nat → Nat)
    (body : ∀ i, i < count → GasSteps (I i) (I (i + 1)))
    (hbody : ∀ i (hi : i < count),
      (body i hi).cost + MachineState.memCost (I i).activeWords.toNat =
        work i + MachineState.memCost (I (i + 1)).activeWords.toNat) :
    (GasSteps.iterateBounded count body).cost +
        MachineState.memCost (I 0).activeWords.toNat =
      (List.range count).foldl (fun total i => total + work i) 0 +
        MachineState.memCost (I count).activeWords.toNat := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [GasSteps.iterateBounded_succ_cost]
      have hp := ih
        (body := fun i hi => body i (Nat.lt_succ_of_lt hi))
        (hbody := fun i hi => hbody i (Nat.lt_succ_of_lt hi))
      have hl := hbody count (Nat.lt_succ_self count)
      simp only [List.range_succ, List.foldl_append, List.foldl]
      omega

def leftLoopWork : Nat :=
  (List.range 80).foldl (fun total i => total + leftIterationWork i) 0

theorem leftLoopWork_eq : leftLoopWork = 71840 := by rfl

def rightRoundSetupWork (i : Nat) : Nat :=
  Meter.runLocatedBlockStaticCost rightRoundPrefixLocated + tableAtWork +
  Meter.runLocatedBlockStaticCost rightRoundMiddleLocated + tableAtWork +
  Meter.runLocatedBlockStaticCost rightRoundSuffixLocated +
    roundWork (rightRoundIndex i)

def rightIterationWork (i : Nat) : Nat :=
  Meter.runLocatedBlockStaticCost rightTestLocated + rightRoundSetupWork i +
    Meter.runLocatedBlockStaticCost rightIncrementLocated

theorem rightRoundSetup_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_rightRoundSetup s messageOffset returnDest rest i hi hstack
      hcode hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      rightRoundSetupWork i + MachineState.memCost
        (rightRoundState s messageOffset returnDest rest i).activeWords.toNat := by
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
  have hq0run : q0.halt = .Running := by simpa [q0, afterConstantLoad] using hrun
  have hq0np : Precompile.isPrecompile q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by simpa [q0, afterConstantLoad] using hnp
  have h0 := blockCost_potential rightRoundPrefixLocated
    (rightBodyAt s messageOffset returnDest rest i)
    (TableTrace.tableAtEntry q0 (UInt256.ofNat 1472) (UInt256.ofNat i)
      (UInt256.ofNat 767) tail1)
    (run_rightRoundPrefix s messageOffset returnDest rest i hi (by omega)
      hcode hrun)
    (by simpa [rightBodyAt] using hfork)
    (by simp [rightRoundPrefixLocated, CopyFree])
  have h1 := tableAt_cost_potential q0 (UInt256.ofNat 1472)
    (UInt256.ofNat i) (UInt256.ofNat 767) tail1
    (by simp [tail1]; omega) hq0code hq0fork hq0run hq0np (by decide)
  have hq1code : q1.executionEnv.code = referenceBytecode := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hcode
  have hq1fork : q1.fork = .Osaka := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad, State.fork] using hfork
  have hq1run : q1.halt = .Running := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hrun
  have hq1np : Precompile.isPrecompile q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, rightFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hnp
  have h2 := blockCost_potential rightRoundMiddleLocated q1
    (TableTrace.tableAtEntry q1 (UInt256.ofNat 1280) (UInt256.ofNat i)
      (UInt256.ofNat 780) tail2)
    (run_rightRoundMiddle s messageOffset returnDest rest i (by omega) hcode hrun)
    (by simpa [q1] using hq1fork)
    (by simp [rightRoundMiddleLocated, CopyFree])
  have h3 := tableAt_cost_potential q1 (UInt256.ofNat 1280)
    (UInt256.ofNat i) (UInt256.ofNat 780) tail2
    (by simp [tail2]; omega) hq1code hq1fork hq1run hq1np (by decide)
  have hq2code : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hcode
  have hq2fork : q2.fork = .Osaka := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad, State.fork] using hfork
  have hq2run : q2.halt = .Running := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hrun
  have hq2np : Precompile.isPrecompile q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, rightSecondReturned, q1, rightFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hnp
  have h4 := blockCost_potential rightRoundSuffixLocated q2
    (RoundTrace.roundEntry q2 (UInt256.ofNat 352) (rightRoundIndex i)
      (TableTrace.tableValue q1 (UInt256.ofNat 1280) (UInt256.ofNat i))
      (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
      (constantAt s 1728 i) (UInt256.ofNat 792) roundTail)
    (run_rightRoundSuffix s messageOffset returnDest rest i (by omega)
      (by omega) hcode hrun)
    (by simpa [q2] using hq2fork)
    (by simp [rightRoundSuffixLocated, CopyFree])
  have h5 := round_cost_potential q2 (UInt256.ofNat 352) (rightRoundIndex i)
    (by unfold rightRoundIndex roundIndex; omega)
    (TableTrace.tableValue q1 (UInt256.ofNat 1280) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
    (constantAt s 1728 i) (UInt256.ofNat 792) roundTail
    (by simp [roundTail]; omega) hq2code hq2fork hq2run hq2np (by decide)
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have h012 := potential_trans _ _ _ _ _ _ _ h01 h2
  have h0123 := potential_trans _ _ _ _ _ _ _ h012 h3
  have h01234 := potential_trans _ _ _ _ _ _ _ h0123 h4
  have hall := potential_trans _ _ _ _ _ _ _ h01234 h5
  simpa [gasSteps_rightRoundSetup, rightRoundSetupWork, rightRoundState,
    rightBodyAt, q0, q1, q2, tail1, tail2, roundTail, GasSteps.trans_cost,
    GasSteps.cast_cost, Nat.add_assoc] using hall

theorem rightIteration_cost_potential (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_rightIterationConcrete s messageOffset returnDest rest i hi hstack
      hcode hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      rightIterationWork i + MachineState.memCost
        (rightRoundState s messageOffset returnDest rest i).activeWords.toNat := by
  let q := rightRoundState s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have h0 := blockCost_potential rightTestLocated
    (rightLoopAt s messageOffset returnDest rest i)
    (rightBodyAt s messageOffset returnDest rest i)
    (run_rightTest_continue s messageOffset returnDest rest i hi (by omega) hrun)
    (by simpa [rightLoopAt] using hfork)
    (by simp [rightTestLocated, CopyFree])
  have h1 := rightRoundSetup_cost_potential s messageOffset returnDest rest i hi
    hstack hcode hfork hrun hnp
  have h2 := blockCost_potential rightIncrementLocated
    (rightRoundReturned q messageOffset returnDest (UInt256.ofNat (roundIndex i))
      rest i)
    (rightLoopAt q messageOffset returnDest rest (i + 1))
    (run_rightIncrement q messageOffset returnDest
      (UInt256.ofNat (roundIndex i)) rest i hi (by omega) hqcode hqrun)
    (by simpa [rightRoundReturned] using hqfork)
    (by simp [rightIncrementLocated, CopyFree])
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have hall := potential_trans _ _ _ _ _ _ _ h01 h2
  simpa [gasSteps_rightIterationConcrete, rightIterationWork, q,
    gasSteps_rightTest_continue, gasSteps_rightIncrement,
    GasSteps.cast_cost, GasSteps.trans_cost, rightLoopAt, rightBodyAt,
    rightRoundState,
    Nat.add_assoc] using hall

def rightLoopWork : Nat :=
  (List.range 80).foldl (fun total i => total + rightIterationWork i) 0

theorem rightLoopWork_eq : rightLoopWork = 72320 := by rfl

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionGasIntegration
