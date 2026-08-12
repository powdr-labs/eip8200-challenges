import Challenge.EvmProof.ProfiledCalls

set_option warningAsError true

/-!
# Caller-profile preservation across one compiled-frame step

The compiler's local instruction helpers expose only `FrameOK` at their
endpoints.  This module recovers the target-only caller profile for a single
real EVM step whose source and target are both the same top-level compiled
frame.  CALL/CREATE entry cannot satisfy the target `FrameOK.callStack`
condition, and a return cannot satisfy the source condition.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

namespace CallerProfile

private def ProfileChain (config : PrecompileConfig) (rootDepth : Nat) :
    ExecutionEnv → List Frame → Prop
  | env, [] =>
      env.precompileConfig = config ∧ env.depth = rootDepth
  | env, frame :: rest =>
      env.precompileConfig = config ∧
        env.depth = frame.executionEnv.depth + 1 ∧
        ProfileChain config rootDepth frame.executionEnv rest

private theorem profileChain_config {config : PrecompileConfig}
    {rootDepth : Nat} {env : ExecutionEnv} {stack : List Frame}
    (h : ProfileChain config rootDepth env stack) :
    env.precompileConfig = config := by
  cases stack <;> exact h.1

private theorem running_executionEnv_or_child {s s' : State}
    (hstep : StepRunning s s') :
    s'.executionEnv = s.executionEnv ∨ s'.callStack ≠ [] := by
  cases hstep <;>
    simp [State.enterCall, State.enterCallFor, State.enterCreate,
      State.calleeEnvFor, State.calleeEnvForCall, State.calleeEnvForCreate,
      State.selfDestructTo]

private theorem profileChain_running {config : PrecompileConfig}
    {rootDepth : Nat} {s s' : State} (hstep : StepRunning s s')
    (hprofile : ProfileChain config rootDepth s.executionEnv s.callStack) :
    ProfileChain config rootDepth s'.executionEnv s'.callStack := by
  cases hstep <;>
    simp_all [ProfileChain, State.enterCall, State.enterCallFor,
      State.enterCreate, State.calleeEnvFor, State.calleeEnvForCall,
      State.calleeEnvForCreate, State.selfDestructTo]
  all_goals exact profileChain_config hprofile

private theorem profileChain_step {config : PrecompileConfig}
    {rootDepth : Nat} {s s' : State} (hstep : Step s s')
    (hprofile : ProfileChain config rootDepth s.executionEnv s.callStack) :
    ProfileChain config rootDepth s'.executionEnv s'.callStack := by
  cases hstep with
  | running _ _ hrun => exact profileChain_running hrun hprofile
  | precompileSuccess => exact hprofile
  | precompileOog => exact hprofile
  | returning hreturn =>
      cases hreturn <;>
        simp_all [ProfileChain, State.resumeSuccess, State.resumeRevert,
          State.resumeException, State.resumeCreateSuccess,
          State.resumeCreateRevert, State.resumeCreateException,
          State.resumeWith]
      all_goals
        split
        · exact hprofile.2.2
        · split <;> exact hprofile.2.2

private theorem profileChain_steps {config : PrecompileConfig}
    {rootDepth : Nat} {s s' : State} (hsteps : Steps s s')
    (hprofile : ProfileChain config rootDepth s.executionEnv s.callStack) :
    ProfileChain config rootDepth s'.executionEnv s'.callStack := by
  induction hsteps with
  | refl => exact hprofile
  | trans hstep _ ih => exact ih (profileChain_step hstep hprofile)

/-- A real EVM step between two top-level compiled-frame states preserves the
call depth and precompile configuration. -/
theorem step_between_frames {config : PrecompileConfig} {code : ByteArray}
    {s s' : State} (hstep : Step s s') (hf : FrameOK code s)
    (hf' : FrameOK code s') (hprofile : CallerProfile config s) :
    CallerProfile config s' := by
  cases hstep with
  | running _ _ hrun =>
      have henv : s'.executionEnv = s.executionEnv :=
        (running_executionEnv_or_child hrun).resolve_right
          (by simp [hf'.callStack])
      exact ⟨by rw [henv]; exact hprofile.depth,
        by rw [henv]; exact hprofile.precompileConfig⟩
  | precompileSuccess => exact ⟨hprofile.depth, hprofile.precompileConfig⟩
  | precompileOog => exact ⟨hprofile.depth, hprofile.precompileConfig⟩
  | returning hreturn =>
      cases hreturn <;> rename_i h_stack _ <;>
        rw [hf.callStack] at h_stack <;> contradiction

/-- A finite real EVM trace between two top-level compiled-frame states
preserves the call depth and precompile configuration, including traces that
temporarily enter and return from child frames. -/
theorem steps_between_frames {config : PrecompileConfig} {code : ByteArray}
    {s s' : State} (hsteps : Steps s s') (hf : FrameOK code s)
    (hf' : FrameOK code s') (hprofile : CallerProfile config s) :
    CallerProfile config s' := by
  have hchain : ProfileChain config s.executionEnv.depth
      s.executionEnv s.callStack := by
    rw [hf.callStack]
    exact ⟨hprofile.precompileConfig, rfl⟩
  have hchain' := profileChain_steps hsteps hchain
  rw [hf'.callStack] at hchain'
  exact ⟨by simpa [hchain'.2] using hprofile.depth, hchain'.1⟩

end CallerProfile

end Challenge.EvmProof
