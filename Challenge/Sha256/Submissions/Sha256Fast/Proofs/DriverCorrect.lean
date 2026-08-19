import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCopy
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCompression

set_option warningAsError true

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper
open MemoryCorrect

noncomputable def gasSteps_block (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    GasSteps s (blockResult s H off endWord rem n rest) :=
  GasSteps.transKnown
    (gasSteps_copy s off endWord rem n rest hcap haw hcode hfork
      hrun hpc hstack hnp)
    (gasSteps_copiedCompression s H off endWord rem n rest hcap
      hcode hfork hrun hnp hH hK)
    33 21167 rfl rfl

@[simp] theorem gasSteps_block_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    (gasSteps_block s H off endWord rem n rest hcap haw hcode hfork hrun hpc
      hstack hnp hH hK).cost = 21200 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect
