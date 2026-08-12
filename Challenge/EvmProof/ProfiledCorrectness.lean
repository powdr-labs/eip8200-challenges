import Challenge.EvmProof.ProfiledLowerCorrect
import Challenge.EvmProof.YulContract
import YulEvmCompiler.Correctness

set_option warningAsError true

/-!
# Profiled Yul compiler correctness

This theorem composes the pinned Yul-to-assembly proof with the local profiled
Phase B.  It differs from `YulEvmCompiler.compile_correct` only by requiring a
caller profile at the initial target state and by routing successful calls
through `ProfiledCallsRealized`.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Outcome Ident VEnv)
open YulSemantics.EVM (U256 EvmState Op evmWithExternal)
open YulEvmCompiler

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-! ### Correctness from explicit compiler certificates -/

/-- End-to-end correctness from the transparent source compiler, explicit
lowering evidence, and an independently checked stack bound.  Unlike
`profiled_compile_correct`, this theorem does not ask the pinned partial
`stackOK2` analyzer to compute. -/
theorem profiled_compiledAssembly_correct {config : PrecompileConfig}
    (hcalls : ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : YulSemantics.Block Op} {asm : List Asm} {is : List Instr}
    (hcompile : compileProgram prog = some asm)
    (hlow : lowerProg (optimizeAsm asm) = some is)
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hbound : ∀ mid, ASteps (optimizeAsm asm)
      ⟨optimizeAsm asm, [], yst0⟩ mid → mid.stk.length ≤ 1023)
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      CallerProfile config s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
    obtain ⟨scope, n0, Γ', n', hh, hnd, hcs, hwf⟩ :=
      compileProgramAsm_inv hcompile
    have hnodup : (labelDefs asm).Nodup := (wfCheck_iff.mp hwf).nodup
    cases hrun with
    | block hbody =>
      have hM := SimA.sim hnodup hbody
      have hout := hM [scope] none none n0 asm Γ' n' trivial trivial hcs
      have hΦ0 : SimA.FEnvOK asm
          (YulSemantics.hoist yulD prog :: []) [scope] :=
        SimA.hoist_ok SimA.FEnvOK.nil hh hnd hcs (List.infix_refl asm)
      have hlen : (assembleBytes is).length = codeSize (optimizeAsm asm) :=
        lowerFrag_length hlow
      have hsmallO : codeSize (optimizeAsm asm) < 256 ^ labelWidth := by
        have hopt := codeSize_optimizeAsm_le asm
        have hsmall := (wfCheck_iff.mp hwf).small
        omega
      cases o with
      | normal =>
        obtain ⟨-, -, hsimS⟩ := hout
        have hsteps0 := (hsimS hΦ0) [] [] [] (by simp)
        simp only [List.append_nil] at hsteps0
        have hstepsO := Peephole.optimizeAsm_asteps hnodup hsteps0
        obtain ⟨bnd, Hb⟩ := profiled_asteps_sim hcalls hcreates hlow hsmallO
          hstepsO (List.suffix_refl (optimizeAsm asm))
          hbound
        refine ⟨bnd, ?_⟩
        intro s0 hf hm hprofile hpc hstk0 hgas
        have hcm0 : ConfMatch (optimizeAsm asm) is
            ⟨optimizeAsm asm, [], yst0⟩ s0 :=
          ⟨by simpa using hf, hm, by rw [hpc]; simp,
            by rw [hstk0]; simp⟩
        obtain ⟨s1, hsteps1, hcm1, -, -⟩ :=
          Hb s0 hcm0 hprofile hgas
        have hpc1 : s1.pc = UInt256.ofNat (assembleBytes is).length := by
          rw [hcm1.pc]
          simp [hlen]
        have hframe1 : FrameOK (assemble is) s1 := by
          simpa using hcm1.frame
        obtain ⟨s2, hstep2, hsm2, hcs2, hhalt2, hret2⟩ :=
          stopStep (is := is) hframe1 hcm1.smatch
            (assemble_eq_mkCode is) hpc1 (by
              have hb := hbound _ hstepsO
              have hp : Operation.pushArity Operation.STOP = 0 := rfl
              have hq : Operation.popArity Operation.STOP = 0 := rfl
              dsimp only at hb
              rw [hcm1.stack]
              simp only [mapStk, List.length_map, hp, hq]
              omega)
        exact ⟨s2, hsteps1.snoc hstep2, hcs2, hsm2,
          Or.inl ⟨rfl, hhalt2, hret2⟩⟩
      | halt =>
        have hAS := hout hΦ0
        obtain ⟨conf, hsteps0, hhalt0⟩ := hAS [] [] [] (by simp)
        simp only [List.append_nil] at hsteps0
        obtain ⟨confO, hstepsO, hhaltO⟩ :=
          Peephole.optimizeAsm_ahalt hnodup hsteps0 hhalt0
        obtain ⟨b1, H1⟩ := profiled_asteps_sim hcalls hcreates hlow
          hsmallO hstepsO (List.suffix_refl (optimizeAsm asm))
          hbound
        obtain ⟨b2, H2⟩ := ahalt_sim hlow hhaltO
          (hstepsO.suffix (List.suffix_refl (optimizeAsm asm)))
          (hbound confO hstepsO)
        refine ⟨b1 + b2, ?_⟩
        intro s0 hf hm hprofile hpc hstk0 hgas
        have hcm0 : ConfMatch (optimizeAsm asm) is
            ⟨optimizeAsm asm, [], yst0⟩ s0 :=
          ⟨by simpa using hf, hm, by rw [hpc]; simp,
            by rw [hstk0]; simp⟩
        obtain ⟨s1, htarget1, hm1, -, hgas1⟩ :=
          H1 s0 hcm0 hprofile (by omega)
        obtain ⟨s2, htarget2, hsm2, hcs2, hhm2⟩ :=
          H2 s1 hm1 (by omega)
        exact ⟨s2, htarget1.append htarget2, hcs2, hsm2,
          Or.inr ⟨rfl, hhm2⟩⟩
      | «break» =>
          rcases hout with ⟨lc, hlc, -⟩
          exact absurd hlc (by simp)
      | «continue» =>
          rcases hout with ⟨lc, hlc, -⟩
          exact absurd hlc (by simp)
      | leave =>
          rcases hout with ⟨fc, hfc, -⟩
          exact absurd hfc (by simp)

/-- Transport a relational source contract through the explicit compiler
certificates. The source postcondition remains attached to its existential Yul
final state; the target execution supplies gas and a matching concrete EVM
state separately. -/
theorem profiled_compiledAssembly_contract_correct {config : PrecompileConfig}
    (hcalls : ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : YulSemantics.Block Op} {asm : List Asm} {is : List Instr}
    (hcompile : compileProgram prog = some asm)
    (hlow : lowerProg (optimizeAsm asm) = some is)
    (hbound : ∀ initial mid, ASteps (optimizeAsm asm)
      ⟨optimizeAsm asm, [], initial⟩ mid → mid.stk.length ≤ 1023)
    {pre : EvmState → Prop}
    {post : EvmState → VEnv yulD → EvmState → Outcome → Prop}
    (contract : YulRunContract yulD prog pre post) :
    ∀ initial, pre initial →
      ∃ finalEnv final outcome,
        post initial finalEnv final outcome ∧
        ∃ b : Nat, ∀ s0 : State,
          FrameOK (assemble is) s0 → StateMatch initial s0 →
          CallerProfile config s0 →
          s0.pc = UInt256.ofNat 0 → s0.stack = [] →
          b ≤ s0.gasAvailable →
          ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch final s' ∧
            ((outcome = .normal ∧ s'.halt = .Success ∧
                s'.hReturn = .empty) ∨
              (outcome = .halt ∧ HaltedMatch final s')) := by
  intro initial hinitial
  obtain ⟨finalEnv, final, outcome, run, result⟩ :=
    contract initial hinitial
  exact ⟨finalEnv, final, outcome, result,
    profiled_compiledAssembly_correct hcalls hcreates hcompile hlow
      (hbound initial) run⟩

/-- End-to-end compiler correctness for a model whose successful calls carry
and preserve the target caller profile. -/
theorem profiled_compile_correct {config : PrecompileConfig}
    (hcalls : ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      CallerProfile config s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  rcases hcompile : compileProgram prog with _ | asm
  · simp [compile, hcompile] at hcomp
  · simp only [compile, hcompile, bind, Option.bind] at hcomp
    obtain ⟨hstk, hlow⟩ :
        stackOK2 (optimizeAsm asm) = true ∧
          lowerProg (optimizeAsm asm) = some is := by
      split at hcomp
      · next h => exact ⟨h, hcomp⟩
      · exact absurd hcomp (by simp)
    exact profiled_compiledAssembly_correct hcalls hcreates hcompile hlow
      (stackOK2_run_bound hstk yst0) hrun

end Challenge.EvmProof
