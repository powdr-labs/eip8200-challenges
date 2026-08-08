import Challenge.Sha256.Submissions.Sha256Fast.Proofs.SchedIter
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.Body
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 100000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.SchedulePathGas

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Meter

private theorem copyFree_of_all {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork))
    (hcert : path.all (fun located => CopyFree located.instruction) = true) :
    ∀ located ∈ path, CopyFree located.instruction :=
  List.all_eq_true.mp hcert

private theorem staticCost_append {artifact : ProgramArtifact} {fork : Fork}
    (left right : List (Located artifact fork)) :
    runLocatedBlockStaticCost (left ++ right) =
      runLocatedBlockStaticCost left + runLocatedBlockStaticCost right := by
  simp [runLocatedBlockStaticCost, List.map_append, List.sum_append]

private theorem compute_eq_pieces : Loop.psched_compute =
    Loop.psched_costStep0 ++ Loop.psched_costStep1 ++
    Loop.psched_costStep2 ++ Loop.psched_costStep3 ++
    Loop.psched_costStep4 ++ Loop.psched_costStep5 ++
    Loop.psched_costStep6 ++ Loop.psched_costStep7 ++
    Loop.psched_costControlSetup := by rfl

private theorem step0_free :
    Loop.psched_costStep0.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem step1_free :
    Loop.psched_costStep1.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem step2_free :
    Loop.psched_costStep2.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem step3_free :
    Loop.psched_costStep3.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem step4_free :
    Loop.psched_costStep4.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem step5_free :
    Loop.psched_costStep5.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem step6_free :
    Loop.psched_costStep6.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem step7_free :
    Loop.psched_costStep7.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem control_free :
    Loop.psched_costControlSetup.all (fun q => CopyFree q.instruction) = true := by rfl

private theorem compute_free :
    Loop.psched_compute.all (fun q => CopyFree q.instruction) = true := by
  rw [compute_eq_pieces]
  simpa using And.intro step0_free
    (And.intro step1_free (And.intro step2_free
      (And.intro step3_free (And.intro step4_free
        (And.intro step5_free (And.intro step6_free
          (And.intro step7_free control_free)))))))

private theorem step0_work :
    runLocatedBlockStaticCost Loop.psched_costStep0 = 143 := by rfl
private theorem step1_work :
    runLocatedBlockStaticCost Loop.psched_costStep1 = 143 := by rfl
private theorem step2_work :
    runLocatedBlockStaticCost Loop.psched_costStep2 = 143 := by rfl
private theorem step3_work :
    runLocatedBlockStaticCost Loop.psched_costStep3 = 143 := by rfl
private theorem step4_work :
    runLocatedBlockStaticCost Loop.psched_costStep4 = 143 := by rfl
private theorem step5_work :
    runLocatedBlockStaticCost Loop.psched_costStep5 = 143 := by rfl
private theorem step6_work :
    runLocatedBlockStaticCost Loop.psched_costStep6 = 143 := by rfl
private theorem step7_work :
    runLocatedBlockStaticCost Loop.psched_costStep7 = 143 := by rfl
private theorem control_work :
    runLocatedBlockStaticCost Loop.psched_costControlSetup = 18 := by rfl

private theorem compute_work :
    runLocatedBlockStaticCost Loop.psched_compute = 1162 := by
  rw [compute_eq_pieces]
  repeat' rw [staticCost_append]
  rw [step0_work, step1_work, step2_work, step3_work, step4_work,
    step5_work, step6_work, step7_work, control_work]

private theorem branch_free :
    Loop.psched_branch.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem branch_work :
    runLocatedBlockStaticCost Loop.psched_branch = 10 := by rfl
private theorem head_free :
    Loop.Body.scheduleHeadPath.all (fun q => CopyFree q.instruction) = true := by rfl
private theorem head_work :
    runLocatedBlockStaticCost Loop.Body.scheduleHeadPath = 1 := by rfl

theorem compute_cost {s t : State}
    (hrun : runLocatedBlock Loop.psched_compute s = some t)
    (hfork : s.fork = .Osaka) (haw : s.activeWords = t.activeWords) :
    runLocatedBlockCost Loop.psched_compute s = 1162 := by
  have h := runLocatedBlock_cost_potential_of_copyFree Loop.psched_compute 1162
    hrun hfork (copyFree_of_all _ compute_free) compute_work
  rw [haw] at h
  omega

theorem branch_cost {s t : State}
    (hrun : runLocatedBlock Loop.psched_branch s = some t)
    (hfork : s.fork = .Osaka) (haw : s.activeWords = t.activeWords) :
    runLocatedBlockCost Loop.psched_branch s = 10 := by
  have h := runLocatedBlock_cost_potential_of_copyFree Loop.psched_branch 10
    hrun hfork (copyFree_of_all _ branch_free) branch_work
  rw [haw] at h
  omega

theorem head_cost {s t : State}
    (hrun : runLocatedBlock Loop.Body.scheduleHeadPath s = some t)
    (hfork : s.fork = .Osaka) (haw : s.activeWords = t.activeWords) :
    runLocatedBlockCost Loop.Body.scheduleHeadPath s = 1 := by
  have h := runLocatedBlock_cost_potential_of_copyFree
    Loop.Body.scheduleHeadPath 1 hrun hfork (copyFree_of_all _ head_free) head_work
  rw [haw] at h
  omega

/-! Small metered wrappers keep the generated execution certificates behind
one definition boundary.  Their cost lemmas inspect only the instruction
meter above; users never need to reduce the large symbolic states. -/

noncomputable def computeTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.psched_compute s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  GasSteps.reprice
    (runLocatedBlock_sound Loop.art .Osaka Loop.psched_compute
      (by simpa [Loop.art] using hcode) hfork hresult hrun hnp)
    1162 (by
      rw [runLocatedBlock_sound_cost]
      exact compute_cost hresult hfork haw)

@[simp] theorem computeTrace_cost {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.psched_compute s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) :
    (computeTrace hcode hfork hresult hrun hnp haw).cost = 1162 := rfl

noncomputable def branchTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.psched_branch s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  GasSteps.reprice
    (runLocatedBlock_sound Loop.art .Osaka Loop.psched_branch
      (by simpa [Loop.art] using hcode) hfork hresult hrun hnp)
    10 (by
      rw [runLocatedBlock_sound_cost]
      exact branch_cost hresult hfork haw)

@[simp] theorem branchTrace_cost {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.psched_branch s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) :
    (branchTrace hcode hfork hresult hrun hnp haw).cost = 10 := rfl

noncomputable def headTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.Body.scheduleHeadPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  GasSteps.reprice
    (runLocatedBlock_sound Loop.art .Osaka Loop.Body.scheduleHeadPath
      (by simpa [Loop.art] using hcode) hfork hresult hrun hnp)
    1 (by
      rw [runLocatedBlock_sound_cost]
      exact head_cost hresult hfork haw)

@[simp] theorem headTrace_cost {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.Body.scheduleHeadPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) :
    (headTrace hcode hfork hresult hrun hnp haw).cost = 1 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.SchedulePathGas
