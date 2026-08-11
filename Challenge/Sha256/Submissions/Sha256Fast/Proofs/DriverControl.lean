import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.GasTools

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverControl

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper
open MemoryCorrect DriverCorrect

private noncomputable def gasSteps_test (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (blockResult s H off endWord rem n rest)
      (testedState s H off endWord rem n rest) :=
  let b := blockResult s H off endWord rem n rest
  let hresult : runLocatedBlock DriverBlocks.fullLoopTestPath b =
      some (testedState s H off endWord rem n rest) := by
    simpa [b, testedState] using DriverBlocks.run_fullLoopTest b
      off endWord rem n rest (by omega)
      (by simpa [b, blockResult, CompressionCorrect.finalState,
        ScheduleTrace.exitState, copiedState] using hrun) rfl rfl
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.fullLoopTestPath 19
    (by rfl) (by rfl)
    (by simpa [b, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState, Loop.art] using hcode)
    (by simpa [b, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hfork)
    hresult
    (by simpa [b, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hrun)
    (by simpa [b, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hnp) rfl

private noncomputable def branchTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.fullLoopBranchPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.fullLoopBranchPath 10
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

noncomputable def gasSteps_continue (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 64 + off) endWord)) :
    GasSteps (blockResult s H off endWord rem n rest)
      (nextFullState s H off endWord rem n rest) :=
  let t := testedState s H off endWord rem n rest
  let gt := gasSteps_test s H off endWord rem n rest hcap
    hcode hfork hrun hnp
  let hresult : runLocatedBlock DriverBlocks.fullLoopBranchPath t =
      some (nextFullState s H off endWord rem n rest) := by
    simpa [t, nextFullState] using
      DriverBlocks.run_fullLoopBranch_continue t
        (UInt256.ofNat 64 + off) endWord rem n rest (by omega)
        (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
          ScheduleTrace.exitState, copiedState] using hcode)
        (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
          ScheduleTrace.exitState, copiedState] using hrun)
        rfl hcond rfl
  let gb := branchTrace
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hcode)
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hfork)
    hresult
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hrun)
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hnp) rfl
  GasSteps.transKnown gt gb 19 10 rfl rfl

@[simp] theorem gasSteps_continue_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 64 + off) endWord)) :
    (gasSteps_continue s H off endWord rem n rest hcap hcode hfork hrun hnp
      hcond).cost = 29 := rfl

noncomputable def gasSteps_exit (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 64 + off) endWord)) :
    GasSteps (blockResult s H off endWord rem n rest)
      (tailState s H off endWord rem n rest) :=
  let t := testedState s H off endWord rem n rest
  let gt := gasSteps_test s H off endWord rem n rest hcap
    hcode hfork hrun hnp
  let hresult : runLocatedBlock DriverBlocks.fullLoopBranchPath t =
      some (tailState s H off endWord rem n rest) := by
    simpa [t, tailState] using DriverBlocks.run_fullLoopBranch_exit t
      (UInt256.ofNat 64 + off) endWord rem n rest (by omega)
      (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
        ScheduleTrace.exitState, copiedState] using hrun)
      rfl hcond rfl
  let gb := branchTrace
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hcode)
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hfork)
    hresult
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hrun)
    (by simpa [t, testedState, blockResult, CompressionCorrect.finalState,
      ScheduleTrace.exitState, copiedState] using hnp) rfl
  GasSteps.transKnown gt gb 19 10 rfl rfl

@[simp] theorem gasSteps_exit_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 64 + off) endWord)) :
    (gasSteps_exit s H off endWord rem n rest hcap hcode hfork hrun hnp
      hcond).cost = 29 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverControl
