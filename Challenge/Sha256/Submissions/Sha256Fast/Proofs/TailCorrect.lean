import Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailOutput

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof
open MemoryCorrect TailState

def shortResult (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  outputResult (shortBranch s off endWord rem n rest) H
    off endWord rem n rest

def longResult (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) : State :=
  let c := cleared s H off endWord rem n rest
  let H1 := firstHash s H off endWord rem n rest
  outputResult c H1 off endWord rem n rest

noncomputable def gasSteps_short (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985) (hrem : rem.toNat < 64)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hshort : UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    GasSteps s (shortResult s H off endWord rem n rest) := by
  let p := prepared s off endWord rem n rest
  let q := shortBranch s off endWord rem n rest
  let gp := TailControl.gasSteps_prepare s off endWord rem n rest hcap haw
    hcode hfork hrun hpc hrem hstack hnp
  let gb := TailControl.gasSteps_shortBranch s off endWord rem n rest hcap
    hcode hfork hrun hnp hshort
  let gl := TailControl.gasSteps_lengthCall q off endWord rem n rest hcap
    (by rfl) (by simpa [q] using hcode) (by simpa [q] using hfork)
    (by simpa [q] using hrun) rfl rfl (by simpa [q] using hnp)
  let gc := TailCompression.gasSteps_finalCompression q H
    off endWord rem n rest hcap (by simpa [q] using hcode)
    (by simpa [q] using hfork) (by simpa [q] using hrun)
    (by simpa [q] using hnp)
    (by simpa [q, shortBranch] using
      prepared_hash s H off endWord rem n rest hrem hH)
    (by simpa [q, shortBranch] using
      prepared_constants s off endWord rem n rest hrem hK)
  let go := TailOutput.gasSteps_output q H off endWord rem n rest hcap
    (by simpa [q] using hcode) (by simpa [q] using hfork)
    (by simpa [q] using hrun) (by simpa [q] using hnp)
  let gco := GasSteps.transKnown gc go 21167 122 (by simp [gc]) (by simp [go])
  let glco := GasSteps.transKnown gl gco 42 21289
    (by apply TailControl.gasSteps_lengthCall_cost) rfl
  let gblco := GasSteps.transKnown gb glco 10 21331 (by simp [gb]) rfl
  simpa [shortResult, q] using
    GasSteps.transKnown gp gblco 46 21341 (by simp [gp]) rfl

noncomputable def gasSteps_long (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985) (hrem : rem.toNat < 64)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hlong : ¬ UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    GasSteps s (longResult s H off endWord rem n rest) := by
  let p := prepared s off endWord rem n rest
  let e := firstEntry s off endWord rem n rest
  let r := firstResult s H off endWord rem n rest
  let c := cleared s H off endWord rem n rest
  let H1 := firstHash s H off endWord rem n rest
  let gp := TailControl.gasSteps_prepare s off endWord rem n rest hcap haw
    hcode hfork hrun hpc hrem hstack hnp
  let gb := TailControl.gasSteps_longBranch s off endWord rem n rest hcap
    hcode hfork hrun hnp hlong
  let ge := TailControl.gasSteps_firstCall s off endWord rem n rest hcap
    hcode hfork hrun hnp
  let gr := TailCompression.gasSteps_firstCompression s H
    off endWord rem n rest hcap hrem hcode hfork hrun hnp hH hK
  let gclear := TailControl.gasSteps_clear s H off endWord rem n rest hcap
    hcode hfork hrun hnp
  let gl := TailControl.gasSteps_lengthCall c off endWord rem n rest hcap
    (by rfl) (by simpa [c] using hcode) (by simpa [c] using hfork)
    (by simpa [c] using hrun) rfl rfl (by simpa [c] using hnp)
  let gc := TailCompression.gasSteps_finalCompression c H1
    off endWord rem n rest hcap (by simpa [c] using hcode)
    (by simpa [c] using hfork) (by simpa [c] using hrun)
    (by simpa [c] using hnp) (cleared_hash s H off endWord rem n rest)
    (cleared_constants s H off endWord rem n rest
      (prepared_constants s off endWord rem n rest hrem hK))
  let go := TailOutput.gasSteps_output c H1 off endWord rem n rest hcap
    (by simpa [c] using hcode) (by simpa [c] using hfork)
    (by simpa [c] using hrun) (by simpa [c] using hnp)
  let gco := GasSteps.transKnown gc go 21167 122 (by simp [gc]) (by simp [go])
  let glco := GasSteps.transKnown gl gco 42 21289
    (by apply TailControl.gasSteps_lengthCall_cost) rfl
  let gclco := GasSteps.transKnown gclear glco 17 21331 (by simp [gclear]) rfl
  let grclco := GasSteps.transKnown gr gclco 21167 21348 (by simp [gr]) rfl
  let gerclco := GasSteps.transKnown ge grclco 14 42515 (by simp [ge]) rfl
  let gberclco := GasSteps.transKnown gb gerclco 10 42529 (by simp [gb]) rfl
  simpa [longResult, c, H1] using
    GasSteps.transKnown gp gberclco 46 42539 (by simp [gp]) rfl

@[simp] theorem gasSteps_short_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985) (hrem : rem.toNat < 64)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hshort : UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    (gasSteps_short s H off endWord rem n rest hcap hrem haw hcode hfork hrun hpc
      hstack hnp hshort hH hK).cost = 21387 := by
  change 46 + (10 + (42 + (21167 + 122))) = 21387
  rfl

@[simp] theorem gasSteps_long_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985) (hrem : rem.toNat < 64)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hlong : ¬ UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hH : HashCorrect s.memory H) (hK : ConstantsCorrect s.memory) :
    (gasSteps_long s H off endWord rem n rest hcap hrem haw hcode hfork hrun hpc
      hstack hnp hlong hH hK).cost = 42585 := by
  change 46 + (10 + (14 + (21167 + (17 + (42 + (21167 + 122)))))) =
    42585
  rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailCorrect
