import YulSemantics.BigStep

set_option warningAsError true

/-! Transport of relational execution across an inserted empty function scope. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics

inductive FunEnvInsertEmpty {D : Dialect} : FunEnv D → FunEnv D → Prop
  | refl (funs : FunEnv D) : FunEnvInsertEmpty funs funs
  | here (funs : FunEnv D) : FunEnvInsertEmpty funs ([] :: funs)
  | underScope (scope : FScope D) {funs funs' : FunEnv D} :
      FunEnvInsertEmpty funs funs' →
      FunEnvInsertEmpty (scope :: funs) (scope :: funs')

private theorem lookupFun_insert {D : Dialect} {funs funs' : FunEnv D}
    (hrel : FunEnvInsertEmpty funs funs') {fn decl cenv}
    (hlookup : lookupFun funs fn = some (decl, cenv)) :
    ∃ cenv', lookupFun funs' fn = some (decl, cenv') ∧
      FunEnvInsertEmpty cenv cenv' := by
  induction hrel with
  | refl => exact ⟨cenv, hlookup, .refl cenv⟩
  | here => exact ⟨cenv, hlookup, .refl cenv⟩
  | underScope scope hrel ih =>
      rw [lookupFun] at hlookup ⊢
      cases hfind : scope.find? (fun p => p.1 = fn) with
      | some found =>
          rw [hfind] at hlookup
          injection hlookup with hp
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hp
          exact ⟨scope :: _, rfl, .underScope scope hrel⟩
      | none =>
          rw [hfind] at hlookup
          exact ih hlookup

theorem step_funEnvInsert {D : Dialect} [DecidableEq D.Value]
    {funs funs' : FunEnv D} {V : VEnv D} {st : D.State}
    {code : Code D.Op} {result : Res D}
    (hstep : Step D funs V st code result)
    (hrel : FunEnvInsertEmpty funs funs') :
    Step D funs' V st code result := by
  induction hstep generalizing funs' with
  | lit => exact Step.lit
  | var hget => exact Step.var hget
  | builtinOk hargs hb ih => exact Step.builtinOk (ih hrel) hb
  | builtinHalt hargs hb ih => exact Step.builtinHalt (ih hrel) hb
  | builtinArgsHalt hargs ih => exact Step.builtinArgsHalt (ih hrel)
  | callOk hargs hlookup hlen hbody hout ihargs ihbody =>
      obtain ⟨cenv', hlookup', hcenv⟩ := lookupFun_insert hrel hlookup
      exact Step.callOk (ihargs hrel) hlookup' hlen (ihbody hcenv) hout
  | callHalt hargs hlookup hlen hbody ihargs ihbody =>
      obtain ⟨cenv', hlookup', hcenv⟩ := lookupFun_insert hrel hlookup
      exact Step.callHalt (ihargs hrel) hlookup' hlen (ihbody hcenv)
  | callArgsHalt hargs ih => exact Step.callArgsHalt (ih hrel)
  | argsNil => exact Step.argsNil
  | argsCons hrest hhead ihrest ihhead =>
      exact Step.argsCons (ihrest hrel) (ihhead hrel)
  | argsRestHalt hrest ih => exact Step.argsRestHalt (ih hrel)
  | argsHeadHalt hrest hhead ihrest ihhead =>
      exact Step.argsHeadHalt (ihrest hrel) (ihhead hrel)
  | funDef => exact Step.funDef
  | block hbody ih => exact Step.block (ih (.underScope _ hrel))
  | letZero => exact Step.letZero
  | letVal hexpr hlen ih => exact Step.letVal (ih hrel) hlen
  | letHalt hexpr ih => exact Step.letHalt (ih hrel)
  | assignVal hexpr hlen ih => exact Step.assignVal (ih hrel) hlen
  | assignHalt hexpr ih => exact Step.assignHalt (ih hrel)
  | exprStmt hexpr ih => exact Step.exprStmt (ih hrel)
  | exprStmtHalt hexpr ih => exact Step.exprStmtHalt (ih hrel)
  | ifTrue hcond hne hbody ihcond ihbody =>
      exact Step.ifTrue (ihcond hrel) hne (ihbody hrel)
  | ifFalse hcond hz ih => exact Step.ifFalse (ih hrel) hz
  | ifHalt hcond ih => exact Step.ifHalt (ih hrel)
  | switchExec hcond hbody ihcond ihbody =>
      exact Step.switchExec (ihcond hrel) (ihbody hrel)
  | switchHalt hcond ih => exact Step.switchHalt (ih hrel)
  | forLoop hinit hloop ihinit ihloop =>
      exact Step.forLoop (ihinit (.underScope _ hrel)) (ihloop (.underScope _ hrel))
  | forInitHalt hinit ih => exact Step.forInitHalt (ih (.underScope _ hrel))
  | «break» => exact Step.break
  | «continue» => exact Step.continue
  | leave => exact Step.leave
  | seqNil => exact Step.seqNil
  | seqCons hhead htail ihhead ihtail =>
      exact Step.seqCons (ihhead hrel) (ihtail hrel)
  | seqStop hhead hne ih => exact Step.seqStop (ih hrel) hne
  | loopDone hcond hz ih => exact Step.loopDone (ih hrel) hz
  | loopCondHalt hcond ih => exact Step.loopCondHalt (ih hrel)
  | loopStep hcond hne hbody hbodyOut hpost hloop
      ihcond ihbody ihpost ihloop =>
      exact Step.loopStep (ihcond hrel) hne (ihbody hrel) hbodyOut
        (ihpost hrel) (ihloop hrel)
  | loopPostHalt hcond hne hbody hbodyOut hpost ihcond ihbody ihpost =>
      exact Step.loopPostHalt (ihcond hrel) hne (ihbody hrel) hbodyOut
        (ihpost hrel)
  | loopBreak hcond hne hbody ihcond ihbody =>
      exact Step.loopBreak (ihcond hrel) hne (ihbody hrel)
  | loopLeave hcond hne hbody ihcond ihbody =>
      exact Step.loopLeave (ihcond hrel) hne (ihbody hrel)
  | loopBodyHalt hcond hne hbody ihcond ihbody =>
      exact Step.loopBodyHalt (ihcond hrel) hne (ihbody hrel)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
