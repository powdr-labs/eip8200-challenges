import Challenge.EvmProof.ProfiledLowerCorrect

set_option warningAsError true

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

example [model : ExternalModel] {config : PrecompileConfig}
    (hcalls : Challenge.EvmProof.ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} (hstep : AStep prog a b) (hsuf : a.code <:+ prog)
    (hcap : a.stk.length ≤ 1023) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      Challenge.EvmProof.CallerProfile config s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) prog is b s' ∧
        Challenge.EvmProof.CallerProfile config s' ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable :=
  Challenge.EvmProof.profiled_astep_sim hcalls hcreates hlow hsmall hstep hsuf hcap

example [model : ExternalModel] {config : PrecompileConfig}
    (hcalls : Challenge.EvmProof.ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} (hsteps : ASteps prog a b) (hsuf : a.code <:+ prog)
    (hbound : ∀ mid, ASteps prog a mid → mid.stk.length ≤ 1023) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      Challenge.EvmProof.CallerProfile config s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) prog is b s' ∧
        Challenge.EvmProof.CallerProfile config s' ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable :=
  Challenge.EvmProof.profiled_asteps_sim hcalls hcreates hlow hsmall hsteps hsuf hbound

/-- info: 'Challenge.EvmProof.profiled_astep_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.profiled_astep_sim

/-- info: 'Challenge.EvmProof.profiled_asteps_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.profiled_asteps_sim
