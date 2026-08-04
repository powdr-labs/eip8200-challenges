import Challenge.Modexp.Reference.Proofs.Bytecode.BigBase
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Certified outer base-conversion loop -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigBaseLoop

open EvmSemantics
open EvmSemantics.EVM
open BigBase

def baseLoopState (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  outerLoop (baseProgress count baseOff i s) accumulator count baseSize
    ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) i

def gasSteps_baseByteAt (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hi : i < baseSize)
    (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (baseLoopState s accumulator count baseSize e m baseOff rest i)
      (baseLoopState s accumulator count baseSize e m baseOff rest (i + 1)) := by
  have hstep := gasSteps_baseByte (baseProgress count baseOff i s)
    accumulator count baseSize e m baseOff i rest hcap hcount hbase hi
    (by omega) (by simpa using hcode) (by simpa using hfork)
    (by simpa using hrun) (by simpa [State.fork] using hnp)
  exact hstep

theorem gasSteps_baseByteAt_cost_potential (s : State)
    (accumulator : UInt256) (count baseSize e m baseOff i : Nat)
    (rest : List UInt256) (hcap : rest.length < 990)
    (hcount : count < 2 ^ 256) (hbase : baseSize < 2 ^ 256)
    (hi : i < baseSize) (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_baseByteAt s accumulator count baseSize e m baseOff i rest hcap
      hcount hbase hi hoff hcode hfork hrun hnp).cost + MachineState.memCost
        (baseLoopState s accumulator count baseSize e m baseOff rest i).activeWords.toNat =
      (3506 + count * 7248) + MachineState.memCost
        (baseLoopState s accumulator count baseSize e m baseOff rest
          (i + 1)).activeWords.toNat := by
  have hstep := gasSteps_baseByte_cost_potential
    (baseProgress count baseOff i s) accumulator count baseSize e m baseOff i
    rest hcap hcount hbase hi (by omega) (by simpa using hcode)
    (by simpa using hfork) (by simpa using hrun)
    (by simpa [State.fork] using hnp)
  exact hstep

def gasSteps_baseLoop (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (baseLoopState s accumulator count baseSize e m baseOff rest 0)
      (baseLoopState s accumulator count baseSize e m baseOff rest baseSize) :=
  Challenge.EvmProof.GasSteps.iterateBounded baseSize fun i hi =>
    gasSteps_baseByteAt s accumulator count baseSize e m baseOff i rest hcap
      hcount hbase hi hoff hcode hfork hrun hnp

theorem gasSteps_baseLoop_cost_potential (s : State)
    (accumulator : UInt256) (count baseSize e m baseOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 990)
    (hcount : count < 2 ^ 256) (hbase : baseSize < 2 ^ 256)
    (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_baseLoop s accumulator count baseSize e m baseOff rest hcap
      hcount hbase hoff hcode hfork hrun hnp).cost + MachineState.memCost
        (baseLoopState s accumulator count baseSize e m baseOff rest
          0).activeWords.toNat =
      baseSize * (3506 + count * 7248) + MachineState.memCost
        (baseLoopState s accumulator count baseSize e m baseOff rest
          baseSize).activeWords.toNat := by
  unfold gasSteps_baseLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  exact gasSteps_baseByteAt_cost_potential s accumulator count baseSize e m
    baseOff i rest hcap hcount hbase hi hoff hcode hfork hrun hnp

private theorem jump944 :
    Decode.isValidJumpDest referenceBytecode 944 = true :=
  Artifact.isValidJumpDest_index 717 (by rfl)

def baseConvertedExit (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256) : State :=
  outerExit (baseProgress count baseOff baseSize s) accumulator count baseSize
    ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)

def initialAccumulator (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (baseConvertedExit s accumulator count baseSize e m baseOff rest)
    2048 3072 1 0 count 944
    ([accumulator, UInt256.ofNat count, UInt256.ofNat baseSize] ++
      ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest))

def gasSteps_baseFinish (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (baseLoopState s accumulator count baseSize e m baseOff rest baseSize)
      (initialAccumulator s accumulator count baseSize e m baseOff rest) := by
  let progress := baseProgress count baseOff baseSize s
  let fullRest := [UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff] ++ rest
  let helperRest := [accumulator, UInt256.ofNat count,
    UInt256.ofNat baseSize] ++ fullRest
  have hhelper : helperRest.length < 1000 := by
    simp [helperRest, fullRest]
    omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka outerGuardPath
      (by simpa [outerLoop, progress, Artifact.referenceArtifact] using hcode)
      (by simpa [outerLoop, progress, State.fork] using hfork)
      (run_outerFinishGuard progress accumulator count baseSize fullRest
        (by simp [fullRest]; omega) hbase (by simpa [progress] using hcode)
        (by simpa [progress] using hrun))
      (by simpa [outerLoop, progress] using hrun)
      (by simpa [outerLoop, progress, State.fork] using hnp)
  have htoAccumulator := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka outerFinishToAccumulatorPath
      (by simpa [outerExit, outerLoop, progress,
        Artifact.referenceArtifact] using hcode)
      (by simpa [outerExit, outerLoop, progress, State.fork] using hfork)
      (run_outerFinishToAccumulator progress accumulator count baseSize fullRest
        (by simp [fullRest]; omega) (by simpa [progress] using hcode)
        (by simpa [progress] using hrun))
      (by simpa [outerExit, outerLoop, progress] using hrun)
      (by simpa [outerExit, outerLoop, progress, State.fork] using hnp)
  have hadd := BigHelpers.gasSteps_addMaskedMod
    (baseConvertedExit s accumulator count baseSize e m baseOff rest)
    2048 3072 1 0 count 944 helperRest hhelper hcount
    (by simpa [baseConvertedExit, outerExit, outerLoop] using hcode)
    (by simpa [baseConvertedExit, outerExit, outerLoop, State.fork] using hfork)
    (by simpa [baseConvertedExit, outerExit, outerLoop] using hrun)
    (by simpa [baseConvertedExit, outerExit, outerLoop, State.fork] using hnp)
    jump944
  exact Challenge.EvmProof.GasSteps.cast
    (hguard.trans (htoAccumulator.trans hadd))
    (by simp [baseLoopState, progress, fullRest])
    (by simp [initialAccumulator, helperRest, fullRest])

set_option linter.unusedSimpArgs false in
theorem gasSteps_baseFinish_cost_potential (s : State)
    (accumulator : UInt256) (count baseSize e m baseOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 990)
    (hcount : count < 2 ^ 256) (hbase : baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_baseFinish s accumulator count baseSize e m baseOff rest hcap
      hcount hbase hcode hfork hrun hnp).cost + MachineState.memCost
        (baseLoopState s accumulator count baseSize e m baseOff rest
          baseSize).activeWords.toNat =
      (206 + count * 453) + MachineState.memCost
        (initialAccumulator s accumulator count baseSize e m baseOff
          rest).activeWords.toNat := by
  let progress := baseProgress count baseOff baseSize s
  let fullRest := [UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff] ++ rest
  let helperRest := [accumulator, UInt256.ofNat count,
    UInt256.ofNat baseSize] ++ fullRest
  have hhelper : helperRest.length < 1000 := by
    simp [helperRest, fullRest]
    omega
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    outerGuardPath 26
      (run_outerFinishGuard progress accumulator count baseSize fullRest
        (by simp [fullRest]; omega) hbase (by simpa [progress] using hcode)
        (by simpa [progress] using hrun))
      (by simpa [outerLoop, progress, State.fork] using hfork)
      (by decide) (by decide)
  have htoAccumulator :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      outerFinishToAccumulatorPath 31
        (run_outerFinishToAccumulator progress accumulator count baseSize
          fullRest (by simp [fullRest]; omega)
          (by simpa [progress] using hcode) (by simpa [progress] using hrun))
        (by simpa [outerExit, outerLoop, progress, State.fork] using hfork)
        (by decide) (by decide)
  have hadd := BigHelpers.gasSteps_addMaskedMod_cost_potential
    (baseConvertedExit s accumulator count baseSize e m baseOff rest)
    2048 3072 1 0 count 944 helperRest hhelper hcount
    (by simpa [baseConvertedExit, outerExit, outerLoop] using hcode)
    (by simpa [baseConvertedExit, outerExit, outerLoop, State.fork] using hfork)
    (by simpa [baseConvertedExit, outerExit, outerLoop] using hrun)
    (by simpa [baseConvertedExit, outerExit, outerLoop, State.fork] using hnp)
    jump944
  unfold gasSteps_baseFinish
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [baseLoopState, baseConvertedExit, initialAccumulator, outerLoop,
    outerExit, BigHelpers.addEntry, progress, fullRest, helperRest] at hguard htoAccumulator hadd ⊢
  omega

def gasSteps_baseConversion (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (baseLoopState s accumulator count baseSize e m baseOff rest 0)
      (initialAccumulator s accumulator count baseSize e m baseOff rest) :=
  (gasSteps_baseLoop s accumulator count baseSize e m baseOff rest hcap hcount
    hbase hoff hcode hfork hrun hnp).trans
  (gasSteps_baseFinish s accumulator count baseSize e m baseOff rest hcap hcount
    hbase hcode hfork hrun hnp)

theorem gasSteps_baseConversion_cost_potential (s : State)
    (accumulator : UInt256) (count baseSize e m baseOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 990)
    (hcount : count < 2 ^ 256) (hbase : baseSize < 2 ^ 256)
    (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_baseConversion s accumulator count baseSize e m baseOff rest hcap
      hcount hbase hoff hcode hfork hrun hnp).cost + MachineState.memCost
        (baseLoopState s accumulator count baseSize e m baseOff rest
          0).activeWords.toNat =
      (baseSize * (3506 + count * 7248) + (206 + count * 453)) +
        MachineState.memCost
          (initialAccumulator s accumulator count baseSize e m baseOff
            rest).activeWords.toNat := by
  exact Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (gasSteps_baseLoop s accumulator count baseSize e m baseOff rest hcap
      hcount hbase hoff hcode hfork hrun hnp)
    (gasSteps_baseFinish s accumulator count baseSize e m baseOff rest hcap
      hcount hbase hcode hfork hrun hnp)
    (baseSize * (3506 + count * 7248)) (206 + count * 453)
    (gasSteps_baseLoop_cost_potential s accumulator count baseSize e m baseOff
      rest hcap hcount hbase hoff hcode hfork hrun hnp)
    (gasSteps_baseFinish_cost_potential s accumulator count baseSize e m baseOff
      rest hcap hcount hbase hcode hfork hrun hnp)

end Challenge.Modexp.Reference.Proofs.Bytecode.BigBaseLoop
