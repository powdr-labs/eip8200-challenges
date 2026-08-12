import Challenge.EvmProof.ProfiledSteps
import YulEvmCompiler.LowerCorrect

set_option warningAsError true

/-!
# Profile-preserving Phase B

This is the minimal specialization of the Yul compiler's assembly-to-EVM
simulation needed by programs that deliberately call a native precompile.
Closed local instructions continue to use the pinned compiler proof.  Only
successful source calls are routed through `ProfiledCallsRealized`; the
caller profile is recovered from the real target trace invariant.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal)
open YulEvmCompiler

@[reducible] private def closedModel : ExternalModel where
  calls := YulSemantics.EVM.ExternalCalls.none
  creates := YulSemantics.EVM.ExternalCreates.none

private theorem closed_astep_profiled {config : PrecompileConfig}
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} (hstep : AStep (model := closedModel) prog a b)
    (hsuf : a.code <:+ prog) (hcap : a.stk.length ≤ 1023) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      CallerProfile config s → bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) prog is b s' ∧
        CallerProfile config s' ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable := by
  obtain ⟨bnd, H⟩ := astep_sim (model := closedModel) ExternalsRealized.none
    hlow hsmall hstep hsuf hcap
  refine ⟨bnd, ?_⟩
  intro s hm hprofile hgas
  obtain ⟨s', hsteps, hm', hgas'⟩ := H s hm hgas
  exact ⟨s', hsteps, hm',
    CallerProfile.steps_between_frames hsteps hm.frame hm'.frame hprofile,
    hgas'⟩

/-- Profile-preserving simulation of one assembly step.  Successful calls use
the supplied profiled relation; all other source steps are simulated through
the compiler's closed local-operation proof. -/
theorem profiled_astep_sim [model : ExternalModel] {config : PrecompileConfig}
    (hcalls : ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} (hstep : AStep prog a b) (hsuf : a.code <:+ prog)
    (hcap : a.stk.length ≤ 1023) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      CallerProfile config s → bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) prog is b s' ∧
        CallerProfile config s' ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable := by
  cases hstep with
  | push =>
      exact closed_astep_profiled hlow hsmall
        (.push (model := closedModel)) hsuf hcap
  | @op yop args rets c σ yst yst' hstepOp =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    simp only [lowerInstr] at hI
    obtain ⟨o, hop, rfl⟩ := Option.map_eq_some_iff.mp hI
    have hpos : codeSize prog - codeSize (Asm.op yop :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    by_cases hcall : IsCallOp yop
    · have hsource := (builtinWithExternal_iff_builtin_of_call hcall).mp hstepOp
      obtain ⟨bnd, H⟩ := hcalls.call hcall hop hsource
      refine ⟨bnd, ?_⟩
      intro s hm hprofile hgas
      have hdec := decoded_op hm.frame (assembleWithPayload_at₁ hbytes payload)
        (by rw [hm.pc, hpos, hlenPre])
        (opTable_roundtrip hop).1 (opTable_roundtrip hop).2
        (opTable_available hop)
      obtain ⟨s', hsteps, hf', hsm', hprofile', hpc', hstk', hgas'⟩ :=
        H hm.frame hm.smatch hprofile hdec
          (by rw [hm.stack, mapStk_words]) hgas
          (by
            have hlen : s.stack.length ≤ 1023 := by
              rw [hm.stack]
              simpa only [mapStk, List.length_map] using hcap
            first
              | ((try simp only [Operation.pushArity, Operation.popArity]); omega)
              | (have := op_arity_bound o; omega))
      refine ⟨s', hsteps, ⟨hf', hsm', ?_, ?_⟩, hprofile', hgas'⟩
      · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
        rw [hpc', hm.pc, hpos]
        have := hf'.codeSmall
        rw [assembleWithPayload, size_mkCode, List.length_append,
          lowerFrag_length hlow] at this
        simp only [Asm.size] at hsize
        rw [succ_ofNat (by omega)]
        congr 1
        omega
      · rw [hstk', mapStk_words]
    · by_cases hcreate : IsCreateOp yop
      · have hsource :=
          (builtinWithExternal_iff_createOnly_of_create hcreate).mp hstepOp
        rw [hcreates] at hsource
        cases yop <;>
          simp_all [IsCreateOp, YulSemantics.EVM.builtinWithExternal,
            YulSemantics.EVM.externalCreate,
            YulSemantics.EVM.ExternalCreates.none]
        case create =>
          rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;>
            contradiction
        case create2 =>
          rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
            contradiction
      · have hnotExternal : ¬ IsExternalOp yop := by
          intro hext
          rcases hext with hcall' | hcreate' | hgas
          · exact hcall hcall'
          · exact hcreate hcreate'
          · subst yop
            simp [opTable] at hop
        have hlocal :=
          (builtinWithExternal_iff_stepOp_of_not_external hnotExternal).mp hstepOp
        refine ⟨opBound yop args, ?_⟩
        intro s hm hprofile hgas
        have hok := opStep hop hlocal
          (σ := mapStk prog σ)
          (assembleWithPayload_at₁ hbytes payload)
          hm.frame hm.smatch
          (by rw [hm.pc, hpos, hlenPre])
          (by rw [hm.stack, mapStk_words])
          (by
            have hlen : s.stack.length ≤ 1023 := by
              rw [hm.stack]
              simpa only [mapStk, List.length_map] using hcap
            first
              | ((try simp only [Operation.pushArity, Operation.popArity]); omega)
              | (have := op_arity_bound o; omega)) hgas
        obtain ⟨s', htargetStep, hf', hsm', hpc', hstk', hgas'⟩ := hok
        have hprofile' := CallerProfile.step_between_frames htargetStep
          hm.frame hf' hprofile
        refine ⟨s', .trans htargetStep (.refl _), ⟨hf', hsm', ?_, ?_⟩,
          hprofile', hgas'⟩
        · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
          rw [hpc', hlenPre]
          exact congrArg UInt256.ofNat (by
            simp only [Asm.size] at hsize
            omega)
        · rw [hstk', mapStk_words]
  | @dup n v τ ρ c yst hτ =>
      exact closed_astep_profiled hlow hsmall
        (.dup (model := closedModel) hτ) hsuf hcap
  | @swap n x y τ ρ c yst hτ =>
      exact closed_astep_profiled hlow hsmall
        (.swap (model := closedModel) hτ) hsuf hcap
  | pop =>
      exact closed_astep_profiled hlow hsmall
        (.pop (model := closedModel)) hsuf hcap
  | label =>
      exact closed_astep_profiled hlow hsmall
        (.label (model := closedModel)) hsuf hcap
  | @jump l c c' σ yst hfind =>
      exact closed_astep_profiled hlow hsmall
        (.jump (model := closedModel) hfind) hsuf hcap
  | @jumpiTaken l v c c' σ yst hv hfind =>
      exact closed_astep_profiled hlow hsmall
        (.jumpiTaken (model := closedModel) hv hfind) hsuf hcap
  | @jumpiFall l v c σ yst hv =>
      exact closed_astep_profiled hlow hsmall
        (.jumpiFall (model := closedModel) hv) hsuf hcap
  | @pushLabel l c σ yst hdef =>
      exact closed_astep_profiled hlow hsmall
        (.pushLabel (model := closedModel) hdef) hsuf hcap
  | @dynJump l c c' σ yst hfind =>
      exact closed_astep_profiled hlow hsmall
        (.dynJump (model := closedModel) hfind) hsuf hcap

/-- Profile-preserving simulation of a finite assembly execution. -/
theorem profiled_asteps_sim [model : ExternalModel] {config : PrecompileConfig}
    (hcalls : ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} (hsteps : ASteps prog a b) (hsuf : a.code <:+ prog)
    (hbound : ∀ mid, ASteps prog a mid → mid.stk.length ≤ 1023) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      CallerProfile config s → bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) prog is b s' ∧
        CallerProfile config s' ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable := by
  induction hsteps with
  | refl a =>
      exact ⟨0, fun s hm hprofile _ =>
        ⟨s, .refl _, hm, hprofile, by omega⟩⟩
  | @head a₁ a₂ a₃ hstep hrest ih =>
      obtain ⟨b₁, H₁⟩ := profiled_astep_sim hcalls hcreates hlow hsmall
        hstep hsuf (hbound a₁ (.refl a₁))
      obtain ⟨b₂, H₂⟩ := ih (hstep.suffix hsuf)
        (fun mid h => hbound mid (.head hstep h))
      refine ⟨b₁ + b₂, ?_⟩
      intro s hm hprofile hgas
      obtain ⟨s₁, htarget₁, hm₁, hprofile₁, hgas₁⟩ :=
        H₁ s hm hprofile (by omega)
      obtain ⟨s₂, htarget₂, hm₂, hprofile₂, hgas₂⟩ :=
        H₂ s₁ hm₁ hprofile₁ (by omega)
      exact ⟨s₂, htarget₁.append htarget₂, hm₂, hprofile₂, by omega⟩

end Challenge.EvmProof
