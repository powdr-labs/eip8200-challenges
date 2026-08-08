import Challenge.EvmProof.Meter
import Challenge.Sha256.Reference.Proofs.Bytecode.Compression

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem noMemoryCost_eq_static (instruction : Instr) (s : State)
    (fork : Fork) (hfork : s.fork = fork) (hfree : CopyFree instruction) :
    Challenge.EvmProof.Meter.instrCostWithoutMemory instruction s =
      Challenge.EvmProof.Meter.instrStaticCost fork instruction := by
  cases instruction with
  | push width value =>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
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

private theorem blockCost_potential_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  apply Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    path hresult hfork
  intro located hmem q hq
  exact noMemoryCost_eq_static located.instruction q fork hq
    (hfree located hmem)

theorem blockCost_potential_of_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      work + MachineState.memCost t.activeWords.toNat := by
  rw [blockCost_potential_static path hresult hfork hfree, hcost]

theorem wAt_cost_potential (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_wAt s index output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      37 + MachineState.memCost
        (Accessors.loadReturned s 800 index returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_load Accessors.wAtPath s 279 800
    index output returnDest rest (Or.inl ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  have hmeter := blockCost_potential_static Accessors.wAtPath hresult hfork
    (by simp [Accessors.wAtPath, CopyFree])
  unfold Accessors.gasSteps_wAt
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Accessors.loadEntry, Accessors.wAtPath,
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost] using hmeter

theorem hAt_cost_potential (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_hAt s index output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      37 + MachineState.memCost
        (Accessors.loadReturned s 288 index returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_load Accessors.hAtPath s 318 288
    index output returnDest rest (Or.inr ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  have hmeter := blockCost_potential_static Accessors.hAtPath hresult hfork
    (by simp [Accessors.hAtPath, CopyFree])
  unfold Accessors.gasSteps_hAt
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Accessors.loadEntry, Accessors.hAtPath,
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost] using hmeter

theorem wSet_cost_potential (s : State) (index value returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_wSet s index value returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      34 + MachineState.memCost
        (Accessors.storeReturned s 800 index value returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_store Accessors.wSetPath s 299 800
    index value returnDest rest (Or.inl ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  have hmeter := blockCost_potential_static Accessors.wSetPath hresult hfork
    (by simp [Accessors.wSetPath, CopyFree])
  unfold Accessors.gasSteps_wSet
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Accessors.storeEntry, Accessors.wSetPath,
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost] using hmeter

theorem hSet_cost_potential (s : State) (index value returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_hSet s index value returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      34 + MachineState.memCost
        (Accessors.storeReturned s 288 index value returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_store Accessors.hSetPath s 338 288
    index value returnDest rest (Or.inr ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  have hmeter := blockCost_potential_static Accessors.hSetPath hresult hfork
    (by simp [Accessors.hSetPath, CopyFree])
  unfold Accessors.gasSteps_hSet
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Accessors.storeEntry, Accessors.hSetPath,
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost] using hmeter

theorem kAt_cost_potential (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_kAt s index output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      43 + MachineState.memCost
        (Accessors.kAtReturned s index returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_kAt s index output returnDest rest hcap
    hcode hrun hvalid
  have hmeter := blockCost_potential_static Accessors.kAtPath hresult hfork
    (by simp [Accessors.kAtPath, CopyFree])
  unfold Accessors.gasSteps_kAt
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Accessors.loadEntry, Accessors.kAtPath,
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost] using hmeter

end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
