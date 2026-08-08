import Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailPrepareGas
import Challenge.EvmProof.FixedPathGas

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailControl

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper
open TailState

private noncomputable def tailBranchTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.tailBranchPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.tailBranchPath 10
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def firstCallTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.firstTailCallPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.firstTailCallPath 14
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def clearTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.clearSecondTailPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.clearSecondTailPath 17
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def lengthCallTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.lengthCallPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.lengthCallPath 42
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

noncomputable def gasSteps_prepare (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hrem : rem.toNat < 64)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (prepared s off endWord rem n rest) :=
  TailPrepareGas.gasSteps_prepare s off endWord rem n rest hcap haw hcode hfork
    hrun hpc hrem hstack hnp

noncomputable def gasSteps_shortBranch (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56))) :
    GasSteps (prepared s off endWord rem n rest)
      (shortBranch s off endWord rem n rest) :=
  let p := prepared s off endWord rem n rest
  let hresult : runLocatedBlock DriverBlocks.tailBranchPath p =
      some (shortBranch s off endWord rem n rest) := by
    simpa [p, shortBranch] using DriverBlocks.run_tailBranch_short p
      off endWord rem n rest (by omega) (by simpa [p] using hcode)
      (by simpa [p] using hrun) rfl hcond rfl
  tailBranchTrace (by simpa [p] using hcode) (by simpa [p] using hfork)
    hresult (by simpa [p] using hrun) (by simpa [p] using hnp) rfl

noncomputable def gasSteps_longBranch (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : ¬ UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56))) :
    GasSteps (prepared s off endWord rem n rest)
      (longBranch s off endWord rem n rest) :=
  let p := prepared s off endWord rem n rest
  let hresult : runLocatedBlock DriverBlocks.tailBranchPath p =
      some (longBranch s off endWord rem n rest) := by
    simpa [p, longBranch] using DriverBlocks.run_tailBranch_long p
      off endWord rem n rest (by omega) (by simpa [p] using hrun)
      rfl hcond rfl
  tailBranchTrace (by simpa [p] using hcode) (by simpa [p] using hfork)
    hresult (by simpa [p] using hrun) (by simpa [p] using hnp) rfl

noncomputable def gasSteps_firstCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (longBranch s off endWord rem n rest)
      (firstEntry s off endWord rem n rest) :=
  let q := longBranch s off endWord rem n rest
  let hresult : runLocatedBlock DriverBlocks.firstTailCallPath q =
      some (firstEntry s off endWord rem n rest) := by
    simpa [q, firstEntry] using DriverBlocks.run_firstTailCall q
      off endWord rem n rest (by omega) (by simpa [q] using hcode)
      (by simpa [q] using hrun) rfl rfl
  firstCallTrace (by simpa [q] using hcode) (by simpa [q] using hfork)
    hresult (by simpa [q] using hrun) (by simpa [q] using hnp) rfl

noncomputable def gasSteps_clear (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (firstResult s H off endWord rem n rest)
      (cleared s H off endWord rem n rest) :=
  let q := firstResult s H off endWord rem n rest
  let hresult : runLocatedBlock DriverBlocks.clearSecondTailPath q =
      some (cleared s H off endWord rem n rest) := by
    simpa [q, cleared] using DriverBlocks.run_clearSecondTail q
      off endWord rem n rest (by omega) rfl (by simpa [q] using hrun) rfl rfl
  clearTrace (by simpa [q] using hcode) (by simpa [q] using hfork)
    hresult (by simpa [q] using hrun) (by simpa [q] using hnp) (by simp)

noncomputable def gasSteps_lengthCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2533)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (lengthEntry s off endWord rem n rest) :=
  let hresult : runLocatedBlock DriverBlocks.lengthCallPath s =
      some (lengthEntry s off endWord rem n rest) := by
    simpa [lengthEntry] using DriverBlocks.run_lengthCall s
      off endWord rem n rest (by omega) haw hcode hrun hpc hstack
  lengthCallTrace hcode hfork hresult hrun hnp
    (by simpa [lengthEntry] using haw)

@[simp] theorem gasSteps_prepare_cost (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hrem : rem.toNat < 64)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_prepare s off endWord rem n rest hcap haw hcode hfork hrun hpc hrem
      hstack hnp).cost = 46 := rfl

@[simp] theorem gasSteps_shortBranch_cost (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56))) :
    (gasSteps_shortBranch s off endWord rem n rest hcap hcode hfork hrun hnp
      hcond).cost = 10 := rfl

@[simp] theorem gasSteps_longBranch_cost (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcond : ¬ UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56))) :
    (gasSteps_longBranch s off endWord rem n rest hcap hcode hfork hrun hnp
      hcond).cost = 10 := rfl

@[simp] theorem gasSteps_firstCall_cost (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_firstCall s off endWord rem n rest hcap hcode hfork hrun hnp).cost =
      14 := rfl

@[simp] theorem gasSteps_clear_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_clear s H off endWord rem n rest hcap hcode hfork hrun hnp).cost =
      17 := rfl

@[simp] theorem gasSteps_lengthCall_cost (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 985)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2533)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_lengthCall s off endWord rem n rest hcap haw hcode hfork hrun hpc
      hstack hnp).cost = 42 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailControl
