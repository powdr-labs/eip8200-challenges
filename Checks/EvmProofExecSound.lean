import Challenge.EvmProof.ExecSound

set_option warningAsError true

open YulSemantics

example {E : ExecDialect} [DecidableEq E.toDialect.Value]
    (hbuiltin : ∀ op args st result,
      E.builtinFn op args st = some result →
        E.toDialect.Builtin op args st result)
    {fuel program st0 V' st' outcome}
    (h : Interp.run E fuel program st0 = .ok (V', st', outcome)) :
    Run E.toDialect program st0 V' st' outcome :=
  Interp.run_sound_of hbuiltin h

example {E : ExecDialect} [DecidableEq E.toDialect.Value]
    {n funs V st fn args argvals st1 decl cenv Vend st2}
    (hargs : Interp.evalArgs E n funs V st args = .ok (.vals argvals st1))
    (hlookup : lookupFun funs fn = some (decl, cenv))
    (hlen : argvals.length = decl.params.length)
    (hbody : Interp.execStmt E n cenv
      (decl.params.zip argvals ++ bindZeros E.toDialect decl.rets)
      st1 (.block decl.body) = .ok (Vend, st2, .normal)) :
    Interp.evalExpr E (n + 1) funs V st (.call fn args) =
      .ok (.vals
        (decl.rets.map (fun r => (VEnv.get Vend r).getD E.toDialect.zero))
        st2) :=
  Interp.evalExpr_call_normal hargs hlookup hlen hbody

example {E : ExecDialect} [DecidableEq E.toDialect.Value]
    {n funs V st head tail V1 st1 Vend st2}
    (hhead : Interp.execStmt E n funs V st head =
      .ok (V1, st1, .normal))
    (htail : Interp.execStmts E n funs V1 st1 tail =
      .ok (Vend, st2, .normal)) :
    Interp.execStmts E (n + 1) funs V st (head :: tail) =
      .ok (Vend, st2, .normal) :=
  Interp.execStmts_cons_normal hhead htail

example {E : ExecDialect} [DecidableEq E.toDialect.Value]
    {n funs V st args V' st' args' fn}
    (hargs : Interp.evalArgs E n funs V st args =
      Interp.evalArgs E n funs V' st' args') :
    Interp.evalExpr E (n + 1) funs V st (.call fn args) =
      Interp.evalExpr E (n + 1) funs V' st' (.call fn args') :=
  Interp.evalExpr_call_of_evalArgs_eq hargs

example {E : ExecDialect} [DecidableEq E.toDialect.Value]
    {n funs funs' V st args V' st' args' fn}
    (hargs : Interp.evalArgs E n funs V st args =
      Interp.evalArgs E n funs' V' st' args')
    (hlookup : lookupFun funs fn = lookupFun funs' fn) :
    Interp.evalExpr E (n + 1) funs V st (.call fn args) =
      Interp.evalExpr E (n + 1) funs' V' st' (.call fn args') :=
  Interp.evalExpr_call_of_evalArgs_lookup_eq hargs hlookup

/-- info: 'YulSemantics.Interp.evalExpr_call_of_evalArgs_lookup_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.evalExpr_call_of_evalArgs_lookup_eq

example {E : ExecDialect} [DecidableEq E.toDialect.Value]
    {n funs V st pre tail V1 st1 Vend st2 outcome}
    (hn : 0 < n)
    (hprefix : Interp.execStmts E (n + pre.length) funs V st pre =
      .ok (V1, st1, .normal))
    (htail : Interp.execStmts E n funs V1 st1 tail =
      .ok (Vend, st2, outcome)) :
    Interp.execStmts E (n + pre.length) funs V st (pre ++ tail) =
      .ok (Vend, st2, outcome) :=
  Interp.execStmts_append_normal hn hprefix htail

/-- info: 'YulSemantics.Interp.execStmts_append_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.execStmts_append_normal

/-- info: 'YulSemantics.Interp.evalExpr_call_of_evalArgs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.evalExpr_call_of_evalArgs_eq

/-- info: 'YulSemantics.Interp.execStmts_cons_normal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms YulSemantics.Interp.execStmts_cons_normal

/-- info: 'YulSemantics.Interp.evalExpr_call_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.evalExpr_call_normal

/-- info: 'YulSemantics.Interp.sound_all_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.sound_all_of

/-- info: 'YulSemantics.Interp.run_sound_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.run_sound_of
