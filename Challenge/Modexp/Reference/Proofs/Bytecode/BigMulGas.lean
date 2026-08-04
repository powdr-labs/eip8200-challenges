import Challenge.Modexp.Reference.Proofs.Bytecode.BigMul
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Aggregate gas theorem for `mulModBig`

Kept separate so the large execution certificate is opaque while its nested
loop costs are composed.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigMul

open EvmSemantics
open EvmSemantics.EVM

private theorem telescope_outer_costs
    (guard load word finish exit p₀ p₁ p₂ p₃ p₄ p₅ work : Nat)
    (hguard : guard + p₀ = 26 + p₁)
    (hload : load + p₁ = 20 + p₂)
    (hword : word + p₂ = work + p₃)
    (hfinish : finish + p₃ = 26 + p₄)
    (hexit : exit + p₄ = 30 + p₅) :
    guard + (load + (word + (finish + exit))) + p₀ =
      (102 + work) + p₅ := by
  omega

private theorem normalize_outer_cost (cost start finish work : Nat)
    (h : cost + start = 26 + (20 + (work + 56)) + finish) :
    cost + start = (102 + work) + finish := by
  omega

theorem gasSteps_mulOuterGuardSegment_cost_potential (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulOuterGuardSegment current a b out modulus count i returnDest
      rest hcap hcount hi hcode hfork hrun hnp).cost + MachineState.memCost
        (mulOuterState current a b out modulus count i returnDest rest).activeWords.toNat =
      26 + MachineState.memCost
        (mulOuterBody current a b out modulus count i returnDest rest).activeWords.toNat := by
  unfold gasSteps_mulOuterGuardSegment
  exact Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterGuardPath 26
      (run_mulOuterGuard current a b out modulus count i returnDest rest
        (by omega) hcount hi hrun)
      (by simpa [mulOuterState, State.fork] using hfork)
      (by decide) (by decide)

theorem gasSteps_mulOuterLoadSegment_cost_potential (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulOuterLoadSegment current a b out modulus count i returnDest
      rest hcap hcount hi hcode hfork hrun hnp).cost + MachineState.memCost
        (mulOuterBody current a b out modulus count i returnDest rest).activeWords.toNat =
      20 + MachineState.memCost
        (mulInnerLoop current a b out modulus count i 0 returnDest rest).activeWords.toNat := by
  unfold gasSteps_mulOuterLoadSegment
  exact Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterLoadPath 20
      (run_mulOuterLoad current a b out modulus count i returnDest rest
        (by omega) (by omega) hrun)
      (by simpa [mulOuterBody, State.fork] using hfork)
      (by decide) (by decide)

theorem gasSteps_mulInnerFinishSegment_cost_potential (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let inner := mulInnerState current word a b out modulus count i 256
      returnDest rest
    (gasSteps_mulInnerFinishSegment current word a b out modulus count i
      returnDest rest hcap hcode hfork hrun hnp).cost +
        MachineState.memCost inner.activeWords.toNat =
      26 + MachineState.memCost ({ inner with pc := UInt256.ofNat 413 }).activeWords.toNat := by
  dsimp only
  unfold gasSteps_mulInnerFinishSegment
  have hm := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerGuardPath 26
      (run_mulWordInnerFinishGuard current word a b out modulus count i
        returnDest rest (by omega) hcode hrun)
      (by simpa [mulInnerState, State.fork] using hfork)
      (by decide) (by decide)
  simpa using hm

theorem gasSteps_mulInnerExitSegment_cost_potential (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let inner := mulInnerState current word a b out modulus count i 256
      returnDest rest
    (gasSteps_mulInnerExitSegment current word a b out modulus count i
      returnDest rest hcap hcount hi hcode hfork hrun hnp).cost +
        MachineState.memCost ({ inner with pc := UInt256.ofNat 413 }).activeWords.toNat =
      30 + MachineState.memCost
        (mulOuterNext inner a b out modulus count i returnDest rest).activeWords.toNat := by
  dsimp only
  unfold gasSteps_mulInnerExitSegment
  exact Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerToOuterPath 30
      (run_mulWordInnerToOuter current word a b out modulus count i returnDest
        rest (by omega) (by omega) hcode hrun)
      (by simpa [mulInnerState, State.fork] using hfork)
      (by decide) (by decide)

/- Direct normalization version retained for audit comparison. -/
/-
theorem gasSteps_mulOuterIteration_cost_potential (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let before := mulOuterProgress current a b out modulus count returnDest rest i
    let after := mulOuterProgress current a b out modulus count returnDest rest (i + 1)
    (gasSteps_mulOuterIteration current a b out modulus count i returnDest rest
        hcap hcount hi hcode hfork hrun hnp).cost +
        MachineState.memCost
          (mulOuterState before a b out modulus count i returnDest rest).activeWords.toNat =
      (102 + 256 * (426 + count * 906)) + MachineState.memCost
        (mulOuterState after a b out modulus count (i + 1) returnDest rest).activeWords.toNat := by
  dsimp only
  let before := mulOuterProgress current a b out modulus count returnDest rest i
  let loaded := mulLoadedState before b i
  let word := mulLoadedWord before b i
  let afterWord := mulWordProgress loaded word a b out modulus count i
    returnDest rest 256
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterGuardPath 26
      (run_mulOuterGuard before a b out modulus count i returnDest rest
        (by omega) hcount hi (by simpa [before] using hrun))
      (by simpa [before, mulOuterState, State.fork] using hfork)
      (by decide) (by decide)
  have hload := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterLoadPath 20
      (run_mulOuterLoad before a b out modulus count i returnDest rest
        (by omega) (by omega) (by simpa [before] using hrun))
      (by simpa [before, mulOuterBody, State.fork] using hfork)
      (by decide) (by decide)
  have hword := gasSteps_mulWordLoop_cost_potential loaded word a b out modulus
    count i returnDest rest hcap hcount
    (by simpa [loaded, mulLoadedState, before] using hcode)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [loaded, mulLoadedState, before] using hrun)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerGuardPath 26
      (run_mulWordInnerFinishGuard afterWord word a b out modulus count i
        returnDest rest (by omega)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hrun))
      (by simpa [afterWord, loaded, mulLoadedState, before, mulInnerState,
        State.fork] using hfork)
      (by decide) (by decide)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerToOuterPath 30
      (run_mulWordInnerToOuter afterWord word a b out modulus count i
        returnDest rest (by omega) (by omega)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hrun))
      (by simpa [afterWord, loaded, mulLoadedState, before, mulInnerState,
        State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_mulOuterIteration gasSteps_mulOuterGuardSegment
    gasSteps_mulOuterLoadSegment gasSteps_mulInnerFinishSegment
    gasSteps_mulInnerExitSegment
  simp only [id_eq, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [before, loaded, word, afterWord] at hguard hload hword hfinish hexit
  simp only [mulOuterState, mulOuterBody, mulInnerLoop_eq_state,
    mulInnerState] at hguard hload hword hfinish hexit ⊢
  simp only [mulOuterProgress] at ⊢
  exact telescope_outer_costs _ _ _ _ _ _ _ _ _ _ _ _ hguard hload hword
    hfinish hexit

-/

theorem gasSteps_mulOuterIteration_cost_potential (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let before := mulOuterProgress current a b out modulus count returnDest rest i
    let after := mulOuterProgress current a b out modulus count returnDest rest (i + 1)
    (gasSteps_mulOuterIteration current a b out modulus count i returnDest rest
        hcap hcount hi hcode hfork hrun hnp).cost + MachineState.memCost
          (mulOuterState before a b out modulus count i returnDest rest).activeWords.toNat =
      (102 + 256 * (426 + count * 906)) + MachineState.memCost
        (mulOuterState after a b out modulus count (i + 1) returnDest rest).activeWords.toNat := by
  dsimp only
  let before := mulOuterProgress current a b out modulus count returnDest rest i
  let loaded := mulLoadedState before b i
  let word := mulLoadedWord before b i
  let afterWord := mulWordProgress loaded word a b out modulus count i
    returnDest rest 256
  let gguard := gasSteps_mulOuterGuardSegment before a b out modulus count i
    returnDest rest hcap hcount hi (by simpa [before] using hcode)
    (by simpa [before, State.fork] using hfork) (by simpa [before] using hrun)
    (by simpa [before, State.fork] using hnp)
  let gloadRaw := gasSteps_mulOuterLoadSegment before a b out modulus count i
    returnDest rest hcap hcount hi (by simpa [before] using hcode)
    (by simpa [before, State.fork] using hfork) (by simpa [before] using hrun)
    (by simpa [before, State.fork] using hnp)
  let gload : Challenge.EvmProof.GasSteps
      (mulOuterBody before a b out modulus count i returnDest rest)
      (mulInnerState loaded word a b out modulus count i 0 returnDest rest) :=
    Challenge.EvmProof.GasSteps.cast gloadRaw rfl (by
      simp only [loaded, word, mulInnerLoop_eq_state])
  let gword := gasSteps_mulWordLoop loaded word a b out modulus count i
    returnDest rest hcap hcount
    (by simpa [loaded, mulLoadedState, before] using hcode)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [loaded, mulLoadedState, before] using hrun)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hnp)
  let gfinish := gasSteps_mulInnerFinishSegment afterWord word a b out modulus
    count i returnDest rest hcap
    (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [afterWord, loaded, mulLoadedState, before] using hrun)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hnp)
  let gexit := gasSteps_mulInnerExitSegment afterWord word a b out modulus
    count i returnDest rest hcap hcount hi
    (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [afterWord, loaded, mulLoadedState, before] using hrun)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hnp)
  have hg := gasSteps_mulOuterGuardSegment_cost_potential before a b out modulus
    count i returnDest rest hcap hcount hi (by simpa [before] using hcode)
    (by simpa [before, State.fork] using hfork) (by simpa [before] using hrun)
    (by simpa [before, State.fork] using hnp)
  have hlRaw := gasSteps_mulOuterLoadSegment_cost_potential before a b out modulus
    count i returnDest rest hcap hcount hi (by simpa [before] using hcode)
    (by simpa [before, State.fork] using hfork) (by simpa [before] using hrun)
    (by simpa [before, State.fork] using hnp)
  have hl : gload.cost + MachineState.memCost
        (mulOuterBody before a b out modulus count i returnDest rest).activeWords.toNat =
      20 + MachineState.memCost
        (mulInnerState loaded word a b out modulus count i 0 returnDest rest).activeWords.toNat := by
    simpa only [gload, Challenge.EvmProof.GasSteps.cast_cost, loaded, word,
      mulInnerLoop_eq_state] using hlRaw
  have hw := gasSteps_mulWordLoop_cost_potential loaded word a b out modulus
    count i returnDest rest hcap hcount
    (by simpa [loaded, mulLoadedState, before] using hcode)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [loaded, mulLoadedState, before] using hrun)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hnp)
  have hf := gasSteps_mulInnerFinishSegment_cost_potential afterWord word a b
    out modulus count i returnDest rest hcap
    (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [afterWord, loaded, mulLoadedState, before] using hrun)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hnp)
  have he := gasSteps_mulInnerExitSegment_cost_potential afterWord word a b out
    modulus count i returnDest rest hcap hcount hi
    (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [afterWord, loaded, mulLoadedState, before] using hrun)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hnp)
  have hfe := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential gfinish
    gexit 26 30 hf he
  have hwfe := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential gword
    (gfinish.trans gexit) (256 * (426 + count * 906)) 56 hw hfe
  have hlwfe := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential gload
    (gword.trans (gfinish.trans gexit)) 20
    (256 * (426 + count * 906) + 56) hl hwfe
  have hall := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential gguard
    (gload.trans (gword.trans (gfinish.trans gexit))) 26
    (20 + (256 * (426 + count * 906) + 56)) hg hlwfe
  unfold gasSteps_mulOuterIteration
  simp only [id_eq, Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost]
  simp only [gguard, gloadRaw, gload, gword, gfinish, gexit, before, loaded,
    word, afterWord, mulOuterProgress, mulOuterState, mulOuterNext,
    mulInnerState,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost] at hall ⊢
  exact normalize_outer_cost _ _ _ _ hall

theorem gasSteps_mulOuterLoop_cost_potential (current : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulOuterLoop current a b out modulus count returnDest rest hcap
        hcount hcode hfork hrun hnp).cost + MachineState.memCost
          (mulOuterState current a b out modulus count 0 returnDest rest).activeWords.toNat =
      count * (102 + 256 * (426 + count * 906)) + MachineState.memCost
        (mulOuterState
          (mulOuterProgress current a b out modulus count returnDest rest count)
          a b out modulus count count returnDest rest).activeWords.toNat := by
  unfold gasSteps_mulOuterLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  simpa using gasSteps_mulOuterIteration_cost_potential current a b out modulus
    count i returnDest rest hcap hcount hi hcode hfork hrun hnp

theorem gasSteps_mulFinish_cost_potential (current : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      returnDest.toNat = true) :
    (gasSteps_mulFinish current a b out modulus count returnDest rest hcap
        hcount hcode hfork hrun hnp hvalid).cost + MachineState.memCost
          (mulOuterState current a b out modulus count count returnDest rest).activeWords.toNat =
      47 + MachineState.memCost
        (mulReturned current returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterGuardPath 26
      (run_mulOuterFinishGuard current a b out modulus count returnDest rest
        (by omega) hcount hcode hrun)
      (by simpa [mulOuterState, State.fork] using hfork)
      (by decide) (by decide)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterExitPath 21
      (run_mulOuterExit current a b out modulus count returnDest rest (by omega)
        hcode hrun hvalid)
      (by simpa [mulOuterState, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_mulFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [mulOuterState, mulReturned] at hguard hexit ⊢
  omega

theorem gasSteps_mulModBig_cost_potential (s : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      returnDest.toNat = true) :
    let copied := mulAfterCopy s a b out modulus count returnDest rest
    let progress := mulOuterProgress copied a b out modulus count returnDest rest count
    (gasSteps_mulModBig s a b out modulus count returnDest rest hcap hcount
        hcode hfork hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      (185 + count * 158 +
          count * (102 + 256 * (426 + count * 906))) +
        MachineState.memCost (mulReturned progress returnDest rest).activeWords.toNat := by
  dsimp only
  let copied := mulAfterCopy s a b out modulus count returnDest rest
  let progress := mulOuterProgress copied a b out modulus count returnDest rest count
  have hinit := gasSteps_mulInitialize_cost_potential s a b out modulus count
    returnDest rest (by omega) hcount hcode hfork hrun hnp
  have hloop := gasSteps_mulOuterLoop_cost_potential copied a b out modulus count
    returnDest rest hcap hcount
    (by simpa [copied, mulAfterCopy, mulAfterClear] using hcode)
    (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
    (by simpa [copied, mulAfterCopy, mulAfterClear] using hrun)
    (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hnp)
  have hfinish := gasSteps_mulFinish_cost_potential progress a b out modulus count
    returnDest rest hcap hcount
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear] using hcode)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear] using hrun)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear, State.fork] using hnp)
    hvalid
  unfold gasSteps_mulModBig
  simp only [id_eq, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [copied, progress] at hinit hloop hfinish
  simp only [mulOuterLoop, mulOuterState] at hinit hloop hfinish ⊢
  omega

end Challenge.Modexp.Reference.Proofs.Bytecode.BigMul
