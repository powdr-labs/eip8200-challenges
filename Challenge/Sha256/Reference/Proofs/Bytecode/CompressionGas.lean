import Challenge.Sha256.Reference.Proofs.Bytecode.CompressionPhasesGas

/-! Exact gas summary for the complete SHA-256 compression bytecode. -/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private theorem potential_trans
    (cost₁ work₁ cost₂ work₂ p₀ p₁ p₂ : Nat)
    (h₁ : cost₁ + p₀ = work₁ + p₁)
    (h₂ : cost₂ + p₁ = work₂ + p₂) :
    (cost₁ + cost₂) + p₀ = (work₁ + work₂) + p₂ := by
  omega

theorem gasSteps_compress_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Compression.gasSteps_compress s msgOff returnDest rest hcap hcode hfork
      hrun hnp hreturn).cost + MachineState.memCost
        (Compression.compressEntry s msgOff returnDest rest).activeWords.toNat =
      155921 + MachineState.memCost
        (Compression.compressResult s msgOff returnDest rest).activeWords.toNat := by
  let prepared := Compression.copyHashState
    (Compression.afterSchedule s msgOff returnDest rest)
  have preparedCode : prepared.executionEnv.code = referenceBytecode := by
    simpa [prepared] using hcode
  have preparedFork : prepared.fork = .Osaka := by
    simpa [prepared, State.fork] using hfork
  have preparedRun : prepared.halt = .Running := by
    simpa [prepared] using hrun
  have preparedNp : Precompile.isPrecompileWithConfig prepared.executionEnv.precompileConfig prepared.executionEnv.fork
      prepared.executionEnv.codeAddr = false := by
    simpa [prepared] using hnp
  have hprepare := prepare_cost_potential s msgOff returnDest rest hcap hcode
    hfork hrun hnp
  have hrounds := roundLoop_cost_potential prepared msgOff returnDest rest hcap
    preparedCode preparedFork preparedRun preparedNp
  let afterRounds := Compression.roundLoopState prepared msgOff returnDest rest 64
  have roundsCode : afterRounds.executionEnv.code = referenceBytecode := by
    simpa [afterRounds] using preparedCode
  have roundsFork : afterRounds.fork = .Osaka := by
    simpa [afterRounds, State.fork] using preparedFork
  have roundsRun : afterRounds.halt = .Running := by
    simpa [afterRounds] using preparedRun
  have roundsNp : Precompile.isPrecompileWithConfig afterRounds.executionEnv.precompileConfig afterRounds.executionEnv.fork
      afterRounds.executionEnv.codeAddr = false := by
    simpa [afterRounds] using preparedNp
  have hexit := roundsExit_cost_potential afterRounds msgOff returnDest rest
    (by omega) roundsCode roundsFork roundsRun roundsNp
  have hfold := foldLoop_cost_potential afterRounds msgOff returnDest rest hcap
    roundsCode roundsFork roundsRun roundsNp
  let afterFold := Compression.foldLoopState afterRounds msgOff returnDest rest 8
  have foldCode : afterFold.executionEnv.code = referenceBytecode := by
    simpa [afterFold] using roundsCode
  have foldFork : afterFold.fork = .Osaka := by
    simpa [afterFold, State.fork] using roundsFork
  have foldRun : afterFold.halt = .Running := by
    simpa [afterFold] using roundsRun
  have foldNp : Precompile.isPrecompileWithConfig afterFold.executionEnv.precompileConfig afterFold.executionEnv.fork
      afterFold.executionEnv.codeAddr = false := by
    simpa [afterFold] using roundsNp
  have hreturnCost := foldExit_cost_potential afterFold msgOff returnDest rest
    (by omega) foldCode foldFork foldRun foldNp hreturn
  rw [Compression.gasSteps_compress_cost]
  have hprepareEnd :
      (Compression.roundAt prepared msgOff returnDest rest 0).activeWords =
        (Compression.roundLoopState prepared msgOff returnDest rest 0).activeWords := by
    rfl
  have hroundExitStart :
      (Compression.roundAt afterRounds msgOff returnDest rest 64).activeWords =
        afterRounds.activeWords := by rfl
  have hfoldStart :
      (Compression.foldAt afterRounds msgOff returnDest rest 0).activeWords =
        (Compression.foldLoopState afterRounds msgOff returnDest rest 0).activeWords := by
    rfl
  have hfoldExitStart :
      (Compression.foldAt afterFold msgOff returnDest rest 8).activeWords =
        afterFold.activeWords := by rfl
  rw [hprepareEnd] at hprepare
  rw [hroundExitStart] at hexit
  rw [hfoldStart] at hexit
  rw [hfoldExitStart] at hreturnCost
  have hresultAW :
      (Compression.compressReturned afterFold returnDest rest).activeWords =
        (Compression.compressResult s msgOff returnDest rest).activeWords := by
    rfl
  rw [hresultAW] at hreturnCost
  have h₁ := potential_trans _ _ _ _ _ _ _ hprepare hrounds
  have h₂ := potential_trans _ _ _ _ _ _ _ h₁ hexit
  have h₃ := potential_trans _ _ _ _ _ _ _ h₂ hfold
  have h₄ := potential_trans _ _ _ _ _ _ _ h₃ hreturnCost
  have hconst : ((((39219 + 64 * 1799) + 31) + 8 * 187) + 39) =
      155921 := by norm_num
  rw [hconst] at h₄
  simpa only [Nat.add_assoc] using h₄

end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
