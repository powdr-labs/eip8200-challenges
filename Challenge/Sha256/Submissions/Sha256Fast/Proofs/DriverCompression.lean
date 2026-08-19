import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverState

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper
open MemoryCorrect

noncomputable def gasSteps_copiedCompression (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    GasSteps (copiedState s off endWord rem n rest)
      (CompressionCorrect.finalState (copiedState s off endWord rem n rest) H
        (UInt256.ofNat 2480) ([off, endWord, rem, n] ++ rest)) :=
  CompressionCorrect.gasSteps_compressBlock
    (copiedState s off endWord rem n rest) H
    (UInt256.ofNat 2480) ([off, endWord, rem, n] ++ rest)
    (by simp; omega) rfl hcode hfork
    (by
      have h := ProgramArtifact.isValidJumpDest_index Loop.art 1386 (by rfl)
      change Decode.isValidJumpDest Loop.bytes 2480 = true at h
      exact h)
    hrun rfl rfl hnp
    (copied_hash s H off endWord rem n rest hH)
    (copied_constants s off endWord rem n rest hK)

@[simp] theorem gasSteps_copiedCompression_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    (gasSteps_copiedCompression s H off endWord rem n rest hcap hcode hfork
      hrun hnp hH hK).cost = 21167 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverCorrect
