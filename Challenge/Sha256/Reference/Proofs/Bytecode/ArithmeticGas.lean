import Challenge.EvmProof.Meter
import Challenge.Sha256.Reference.Proofs.Bytecode.BigSigma

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.ArithmeticGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem instrCostWithoutMemory_eq_static (instruction : Instr) (s : State)
    (hfork : s.fork = .Osaka) (hfree : CopyFree instruction) :
    Challenge.EvmProof.Meter.instrCostWithoutMemory instruction s =
      Challenge.EvmProof.Meter.instrStaticCost .Osaka instruction := by
  cases instruction with
  | push width value => simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | CompBit op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Keccak op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Env op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Block op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Push op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Dup op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Swap op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | DupN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | SwapN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Exchange op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Log op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | System op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]

private theorem block_cost_potential
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  apply Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    path hresult hfork
  intro located hmem q hq
  exact instrCostWithoutMemory_eq_static located.instruction q hq
    (hfree located hmem)

private theorem block_cost_of_activeWords_eq
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction)
    (hwords : t.activeWords = s.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path := by
  have hpotential := block_cost_potential path hresult hfork hfree
  rw [hwords] at hpotential
  omega

/-! ### Costs of the two big-sigma blocks

The old six theorems here priced `ch`, `maj`, `ssig0`, `ssig1` and the two
big sigmas as sequences of `rotr` *calls*.  With the rotations inlined there are
no calls to price: each big-sigma block is one straight run, and its cost is its
static cost — 114 for the inlined `Sigma1`, 132 for the called `Sigma0` (which
still pays for its entry `JUMPDEST` and returning `JUMP`).

`ch`, `maj`, `ssig0` and `ssig1` are inlined into the round body and the schedule
respectively, so their costs now belong to those blocks rather than here. -/

private theorem sigma1_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.sigma1Path = 114 := by rfl

private theorem sigma0_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.sigma0Path = 132 := by rfl

theorem gasSteps_sigma1_cost (s : State) (v0 v1 x : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : (BigSigma.sigma1Entry s v0 v1 x rest).executionEnv.code =
      referenceBytecode)
    (hfork : (BigSigma.sigma1Entry s v0 v1 x rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (BigSigma.sigma1Entry s v0 v1 x rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (BigSigma.sigma1Entry s v0 v1 x rest).executionEnv.precompileConfig
      (BigSigma.sigma1Entry s v0 v1 x rest).executionEnv.fork
      (BigSigma.sigma1Entry s v0 v1 x rest).executionEnv.codeAddr = false) :
    (BigSigma.gasSteps_sigma1 s v0 v1 x rest hcap hcode hfork hrun hhalt
      hnp).cost = 114 := by
  have h := block_cost_of_activeWords_eq BigSigma.sigma1Path
    (BigSigma.run_sigma1 s v0 v1 x rest hcap hrun) hfork
    (by simp [BigSigma.sigma1Path, CopyFree]) (by rfl)
  rw [sigma1_static] at h
  simpa [BigSigma.gasSteps_sigma1,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    BigSigma.sigma1Entry] using h

theorem gasSteps_sigma0_cost (s : State) (x returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : (BigSigma.sigma0Entry s x returnDest rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (BigSigma.sigma0Entry s x returnDest rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (BigSigma.sigma0Entry s x returnDest rest).executionEnv.precompileConfig
      (BigSigma.sigma0Entry s x returnDest rest).executionEnv.fork
      (BigSigma.sigma0Entry s x returnDest rest).executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (BigSigma.gasSteps_sigma0 s x returnDest rest hcap hcode hfork hrun hhalt
      hnp hvalid).cost = 132 := by
  have h := block_cost_of_activeWords_eq BigSigma.sigma0Path
    (BigSigma.run_sigma0 s x returnDest rest hcap hrun hvalid hcode) hfork
    (by simp [BigSigma.sigma0Path, CopyFree]) (by rfl)
  rw [sigma0_static] at h
  simpa [BigSigma.gasSteps_sigma0,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    BigSigma.sigma0Entry] using h

end Challenge.Sha256.Reference.Proofs.Bytecode.ArithmeticGas
