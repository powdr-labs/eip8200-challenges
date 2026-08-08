import Challenge.EvmProof.Meter

set_option warningAsError true

namespace Challenge.EvmProof.FixedPathGas

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Meter

/-- A successful copy-free path together with its memory-potential equation.
Unlike `trace`, this form permits the active-memory high-water mark to grow. -/
noncomputable def tracePotential {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (work : Nat)
    (_hfree : path.all (fun q => CopyFree q.instruction) = true)
    (_hwork : runLocatedBlockStaticCost path = work) {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t :=
  runLocatedBlock_sound artifact fork path hcode hfork hresult hrun hnp

@[simp] theorem tracePotential_cost {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (work : Nat)
    (hfree : path.all (fun q => CopyFree q.instruction) = true)
    (hwork : runLocatedBlockStaticCost path = work) {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (tracePotential path work hfree hwork hcode hfork hresult hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      work + MachineState.memCost t.activeWords.toNat := by
  rw [tracePotential, runLocatedBlock_sound_cost]
  exact runLocatedBlock_cost_potential_of_copyFree path work hresult hfork
    (List.all_eq_true.mp hfree) hwork

/-- Exact-cost specialization of `tracePotential` when both endpoint memory
high-water marks are known. -/
noncomputable def traceGrowing {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (work cost startWords endWords : Nat)
    (hfree : path.all (fun q => CopyFree q.instruction) = true)
    (hwork : runLocatedBlockStaticCost path = work)
    (hcost : cost + MachineState.memCost startWords =
      work + MachineState.memCost endWords) {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstart : s.activeWords.toNat = startWords)
    (hend : t.activeWords.toNat = endWords) : GasSteps s t :=
  let raw := tracePotential path work hfree hwork hcode hfork hresult hrun hnp
  GasSteps.reprice raw cost (by
    dsimp [raw]
    have h := tracePotential_cost path work hfree hwork hcode hfork hresult
      hrun hnp
    rw [hstart, hend] at h
    omega)

@[simp] theorem traceGrowing_cost {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (work cost startWords endWords : Nat)
    (hfree : path.all (fun q => CopyFree q.instruction) = true)
    (hwork : runLocatedBlockStaticCost path = work)
    (hcost : cost + MachineState.memCost startWords =
      work + MachineState.memCost endWords) {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstart : s.activeWords.toNat = startWords)
    (hend : t.activeWords.toNat = endWords) :
    (traceGrowing path work cost startWords endWords hfree hwork hcost hcode hfork
      hresult hrun hnp hstart hend).cost = cost := rfl

/-- Turn a successful copy-free symbolic path into a certificate whose exact
static cost is definitionally visible.  Equal endpoint memory high-water
marks discharge the EVM memory-expansion potential. -/
noncomputable def trace {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (cost : Nat)
    (hfree : path.all (fun q => CopyFree q.instruction) = true)
    (hwork : runLocatedBlockStaticCost path = cost) {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  GasSteps.reprice
    (runLocatedBlock_sound artifact fork path hcode hfork hresult hrun hnp)
    cost (by
      rw [runLocatedBlock_sound_cost]
      have h := runLocatedBlock_cost_potential_of_copyFree path cost
        hresult hfork (List.all_eq_true.mp hfree) hwork
      rw [haw] at h
      omega)

@[simp] theorem trace_cost {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (cost : Nat)
    (hfree : path.all (fun q => CopyFree q.instruction) = true)
    (hwork : runLocatedBlockStaticCost path = cost) {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) :
    (trace path cost hfree hwork hcode hfork hresult hrun hnp haw).cost = cost :=
  rfl

end Challenge.EvmProof.FixedPathGas
