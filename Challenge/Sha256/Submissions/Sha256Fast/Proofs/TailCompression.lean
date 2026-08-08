import Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailControl

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailCompression

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper
open MemoryCorrect TailState

noncomputable def gasSteps_firstCompression (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985) (hrem : rem.toNat < 64)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    GasSteps (firstEntry s off endWord rem n rest)
      (firstResult s H off endWord rem n rest) := by
  unfold firstResult
  apply CompressionCorrect.gasSteps_compressBlock
  · simp
    omega
  · rfl
  · simpa using hcode
  · simpa using hfork
  · have h := ProgramArtifact.isValidJumpDest_index Loop.art 1412 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2522 = true at h
    exact h
  · simpa using hrun
  · rfl
  · rfl
  · simpa using hnp
  · simpa [firstEntry, longBranch] using
      prepared_hash s H off endWord rem n rest hrem hH
  · simpa [firstEntry, longBranch] using
      prepared_constants s off endWord rem n rest hrem hK

noncomputable def gasSteps_finalCompression (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    GasSteps (lengthEntry s off endWord rem n rest)
      (finalResult s H off endWord rem n rest) := by
  unfold finalResult
  apply CompressionCorrect.gasSteps_compressBlock
  · simp
    omega
  · rfl
  · simpa using hcode
  · simpa using hfork
  · have h := ProgramArtifact.isValidJumpDest_index Loop.art 1432 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2562 = true at h
    exact h
  · simpa using hrun
  · rfl
  · rfl
  · simpa using hnp
  · exact lengthEntry_hash s H off endWord rem n rest hH
  · exact lengthEntry_constants s off endWord rem n rest hK

@[simp] theorem gasSteps_firstCompression_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985) (hrem : rem.toNat < 64)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    (gasSteps_firstCompression s H off endWord rem n rest hcap hrem hcode hfork
      hrun hnp hH hK).cost = 21167 := rfl

@[simp] theorem gasSteps_finalCompression_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    (gasSteps_finalCompression s H off endWord rem n rest hcap hcode hfork hrun
      hnp hH hK).cost = 21167 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailCompression
