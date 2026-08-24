import YulSemantics.Adequacy

set_option warningAsError true

/-!
# One-way soundness for executable Yul sub-dialects

The upstream adequacy theorem asks an executable evaluator to characterize
its relational dialect in both directions.  Proof-oriented deterministic
sub-dialects of an open-world relation only need the forward direction:
every result they compute is admitted by that relation.  This module exposes
that strictly weaker, reusable soundness boundary.
-/

namespace YulSemantics.Interp

variable {E : ExecDialect} [DecidableEq E.toDialect.Value]

/-- Evaluate a function call from already-checked argument, lookup, arity,
and normally completed body stages.  This keeps large concrete function
environments opaque while their bodies are proved one statement at a time. -/
theorem evalExpr_call_normal
    {n funs V st fn args argvals st1 decl cenv Vend st2}
    (hargs : evalArgs E n funs V st args = .ok (.vals argvals st1))
    (hlookup : lookupFun funs fn = some (decl, cenv))
    (hlen : argvals.length = decl.params.length)
    (hbody : execStmt E n cenv
      (decl.params.zip argvals ++ bindZeros E.toDialect decl.rets)
      st1 (.block decl.body) = .ok (Vend, st2, .normal)) :
    evalExpr E (n + 1) funs V st (.call fn args) =
      .ok (.vals
        (decl.rets.map (fun r => (VEnv.get Vend r).getD E.toDialect.zero))
        st2) := by
  simp [evalExpr, hargs, hlookup, hlen, hbody]

/-- Execute a nonempty statement sequence from separately checked head and
tail stages.  Concrete source proofs use this to keep each statement opaque. -/
theorem execStmts_cons_normal
    {n funs V st head tail V1 st1 Vend st2}
    (hhead : execStmt E n funs V st head = .ok (V1, st1, .normal))
    (htail : execStmts E n funs V1 st1 tail =
      .ok (Vend, st2, .normal)) :
    execStmts E (n + 1) funs V st (head :: tail) =
      .ok (Vend, st2, .normal) := by
  simp [execStmts, hhead, htail]

/-- Function-call evaluation depends on its argument expressions only through
the argument evaluator's result. -/
theorem evalExpr_call_of_evalArgs_eq
    {n funs V st args V' st' args' fn}
    (hargs : evalArgs E n funs V st args =
      evalArgs E n funs V' st' args') :
    evalExpr E (n + 1) funs V st (.call fn args) =
      evalExpr E (n + 1) funs V' st' (.call fn args') := by
  simp only [evalExpr]
  rw [hargs]

/-- The call evaluator can also move between function environments when both
argument evaluation and lookup agree. -/
theorem evalExpr_call_of_evalArgs_lookup_eq
    {n funs funs' V st args V' st' args' fn}
    (hargs : evalArgs E n funs V st args =
      evalArgs E n funs' V' st' args')
    (hlookup : lookupFun funs fn = lookupFun funs' fn) :
    evalExpr E (n + 1) funs V st (.call fn args) =
      evalExpr E (n + 1) funs' V' st' (.call fn args') := by
  simp only [evalExpr]
  rw [hargs, hlookup]

/-- A normally completed prefix can be spliced in front of a separately
checked tail when the starting fuel accounts for the prefix length. -/
theorem execStmts_append_normal
    {n funs V st pre tail V1 st1 Vend st2 outcome}
    (hn : 0 < n)
    (hpre : execStmts E (n + pre.length) funs V st pre =
      .ok (V1, st1, .normal))
    (htail : execStmts E n funs V1 st1 tail =
      .ok (Vend, st2, outcome)) :
    execStmts E (n + pre.length) funs V st (pre ++ tail) =
      .ok (Vend, st2, outcome) := by
  induction pre generalizing n V st with
  | nil =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [List.length_nil, Nat.add_zero, List.nil_append] at hpre ⊢
          simp only [execStmts] at hpre
          cases Result.ok.inj hpre
          exact htail
  | cons head rest ih =>
      have hfuel : n + (head :: rest).length =
          (n + rest.length) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hfuel] at hpre ⊢
      simp only [List.cons_append, execStmts] at hpre ⊢
      cases hhead : execStmt E (n + rest.length) funs V st head with
      | stuck => simp [hhead] at hpre
      | outOfFuel => simp [hhead] at hpre
      | ok result =>
          rcases result with ⟨Vhead, stHead, headOutcome⟩
          cases headOutcome <;> simp [hhead] at hpre ⊢
          exact ih hn hpre htail

theorem sound_all_of
    (hE : ∀ op args st result, E.builtinFn op args st = some result →
      E.toDialect.Builtin op args st result) : ∀ n : Nat,
    (∀ funs V st e r, evalExpr E n funs V st e = .ok r →
        EvalExpr E.toDialect funs V st e r) ∧
    (∀ funs V st es r, evalArgs E n funs V st es = .ok r →
        EvalArgs E.toDialect funs V st es r) ∧
    (∀ funs V st s V' st' o, execStmt E n funs V st s = .ok (V', st', o) →
        ExecStmt E.toDialect funs V st s V' st' o) ∧
    (∀ funs V st ss V' st' o, execStmts E n funs V st ss = .ok (V', st', o) →
        ExecStmts E.toDialect funs V st ss V' st' o) ∧
    (∀ funs V st c post body V' st' o, execLoop E n funs V st c post body = .ok (V', st', o) →
        ExecLoop E.toDialect funs V st c post body V' st' o) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro funs V st e r h; simp [evalExpr] at h
      · intro funs V st es r h; simp [evalArgs] at h
      · intro funs V st s V' st' o h; simp [execStmt] at h
      · intro funs V st ss V' st' o h; simp [execStmts] at h
      · intro funs V st c post body V' st' o h; simp [execLoop] at h
  | succ n ih =>
      obtain ⟨ihE, ihA, ihS, ihSS, ihL⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      /- ### Expressions -/
      · intro funs V st e r h
        cases e with
        | lit l =>
            simp only [evalExpr] at h
            injection h with h; subst h
            exact Step.lit
        | var x =>
            cases hv : VEnv.get V x with
            | none => simp [evalExpr, hv] at h
            | some v =>
                simp only [evalExpr, hv] at h
                injection h with h; subst h
                exact Step.var hv
        | builtin op args =>
            simp only [evalExpr] at h
            cases hA : evalArgs E n funs V st args with
            | stuck => simp [hA] at h
            | outOfFuel => simp [hA] at h
            | ok a =>
                cases a with
                | vals argvals st1 =>
                    cases hB : E.builtinFn op argvals st1 with
                    | none => simp [hA, hB] at h
                    | some br =>
                        cases br with
                        | ok rets st2 =>
                            simp [hA, hB] at h; subst h
                            exact Step.builtinOk (ihA _ _ _ _ _ hA) (hE _ _ _ _ hB)
                        | halt st2 =>
                            simp [hA, hB] at h; subst h
                            exact Step.builtinHalt (ihA _ _ _ _ _ hA) (hE _ _ _ _ hB)
                | halt st1 =>
                    simp [hA] at h; subst h
                    exact Step.builtinArgsHalt (ihA _ _ _ _ _ hA)
        | call fn args =>
            simp only [evalExpr] at h
            cases hA : evalArgs E n funs V st args with
            | stuck => simp [hA] at h
            | outOfFuel => simp [hA] at h
            | ok a =>
                cases a with
                | vals argvals st1 =>
                    cases hL : lookupFun funs fn with
                    | none => simp [hA, hL] at h
                    | some p =>
                        obtain ⟨decl, cenv⟩ := p
                        by_cases hlen : argvals.length = decl.params.length
                        · cases hS : execStmt E n cenv
                              (decl.params.zip argvals ++ bindZeros E.toDialect decl.rets) st1
                              (.block decl.body) with
                          | stuck => simp [hA, hL, hlen, hS] at h
                          | outOfFuel => simp [hA, hL, hlen, hS] at h
                          | ok x =>
                              obtain ⟨Vend, st2, o⟩ := x
                              cases o with
                              | normal =>
                                  simp [hA, hL, hlen, hS] at h; subst h
                                  exact Step.callOk (ihA _ _ _ _ _ hA) hL hlen
                                    (ihS _ _ _ _ _ _ _ hS) (Or.inl rfl)
                              | leave =>
                                  simp [hA, hL, hlen, hS] at h; subst h
                                  exact Step.callOk (ihA _ _ _ _ _ hA) hL hlen
                                    (ihS _ _ _ _ _ _ _ hS) (Or.inr rfl)
                              | halt =>
                                  simp [hA, hL, hlen, hS] at h; subst h
                                  exact Step.callHalt (ihA _ _ _ _ _ hA) hL hlen
                                    (ihS _ _ _ _ _ _ _ hS)
                              | «break» => simp [hA, hL, hlen, hS] at h
                              | «continue» => simp [hA, hL, hlen, hS] at h
                        · simp [hA, hL, hlen] at h
                | halt st1 =>
                    simp [hA] at h; subst h
                    exact Step.callArgsHalt (ihA _ _ _ _ _ hA)
      /- ### Argument lists -/
      · intro funs V st es r h
        cases es with
        | nil =>
            simp only [evalArgs] at h
            injection h with h; subst h
            exact Step.argsNil
        | cons e rest =>
            simp only [evalArgs] at h
            cases hR : evalArgs E n funs V st rest with
            | stuck => simp [hR] at h
            | outOfFuel => simp [hR] at h
            | ok a =>
                cases a with
                | vals restvals st1 =>
                    cases hH : evalExpr E n funs V st1 e with
                    | stuck => simp [hR, hH] at h
                    | outOfFuel => simp [hR, hH] at h
                    | ok b =>
                        cases b with
                        | vals vs st2 =>
                            cases vs with
                            | nil => simp [hR, hH] at h
                            | cons v vs' =>
                                cases vs' with
                                | nil =>
                                    simp [hR, hH] at h; subst h
                                    exact Step.argsCons (ihA _ _ _ _ _ hR) (ihE _ _ _ _ _ hH)
                                | cons _ _ => simp [hR, hH] at h
                        | halt st2 =>
                            simp [hR, hH] at h; subst h
                            exact Step.argsHeadHalt (ihA _ _ _ _ _ hR) (ihE _ _ _ _ _ hH)
                | halt st1 =>
                    simp [hR] at h; subst h
                    exact Step.argsRestHalt (ihA _ _ _ _ _ hR)
      /- ### Statements -/
      · intro funs V st s V' st' o h
        cases s with
        | funDef n' ps rs b =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.funDef
        | block body =>
            simp only [execStmt] at h
            cases hB : execStmts E n (hoist E.toDialect body :: funs) V st body with
            | stuck => simp [hB] at h
            | outOfFuel => simp [hB] at h
            | ok x =>
                obtain ⟨Vb, stb, ob⟩ := x
                simp [hB] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact Step.block (ihSS _ _ _ _ _ _ _ hB)
        | letDecl vars val =>
            cases val with
            | none =>
                simp only [execStmt] at h
                injection h with h
                obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
                exact Step.letZero
            | some e =>
                simp only [execStmt] at h
                cases hEv : evalExpr E n funs V st e with
                | stuck => simp [hEv] at h
                | outOfFuel => simp [hEv] at h
                | ok a =>
                    cases a with
                    | vals vals st1 =>
                        by_cases hlen : vals.length = vars.length
                        · simp [hEv, hlen] at h
                          obtain ⟨rfl, rfl, rfl⟩ := h
                          exact Step.letVal (ihE _ _ _ _ _ hEv) hlen
                        · simp [hEv, hlen] at h
                    | halt st1 =>
                        simp [hEv] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact Step.letHalt (ihE _ _ _ _ _ hEv)
        | assign vars e =>
            simp only [execStmt] at h
            cases hEv : evalExpr E n funs V st e with
            | stuck => simp [hEv] at h
            | outOfFuel => simp [hEv] at h
            | ok a =>
                cases a with
                | vals vals st1 =>
                    by_cases hlen : vals.length = vars.length
                    · simp [hEv, hlen] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      exact Step.assignVal (ihE _ _ _ _ _ hEv) hlen
                    · simp [hEv, hlen] at h
                | halt st1 =>
                    simp [hEv] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.assignHalt (ihE _ _ _ _ _ hEv)
        | exprStmt e =>
            simp only [execStmt] at h
            cases hEv : evalExpr E n funs V st e with
            | stuck => simp [hEv] at h
            | outOfFuel => simp [hEv] at h
            | ok a =>
                cases a with
                | vals vs st1 =>
                    cases vs with
                    | nil =>
                        simp [hEv] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact Step.exprStmt (ihE _ _ _ _ _ hEv)
                    | cons _ _ => simp [hEv] at h
                | halt st1 =>
                    simp [hEv] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.exprStmtHalt (ihE _ _ _ _ _ hEv)
        | cond c body =>
            simp only [execStmt] at h
            cases hC : evalExpr E n funs V st c with
            | stuck => simp [hC] at h
            | outOfFuel => simp [hC] at h
            | ok a =>
                cases a with
                | vals vs st1 =>
                    cases vs with
                    | nil => simp [hC] at h
                    | cons cv vs' =>
                        cases vs' with
                        | cons _ _ => simp [hC] at h
                        | nil =>
                            by_cases hz : cv = E.toDialect.zero
                            · simp [hC, hz] at h
                              obtain ⟨rfl, rfl, rfl⟩ := h
                              exact Step.ifFalse (ihE _ _ _ _ _ hC) hz
                            · simp only [hC, Result.ok_bind] at h
                              rw [if_neg hz] at h
                              exact Step.ifTrue (ihE _ _ _ _ _ hC) hz (ihS _ _ _ _ _ _ _ h)
                | halt st1 =>
                    simp [hC] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.ifHalt (ihE _ _ _ _ _ hC)
        | switch c cases' dflt =>
            simp only [execStmt] at h
            cases hC : evalExpr E n funs V st c with
            | stuck => simp [hC] at h
            | outOfFuel => simp [hC] at h
            | ok a =>
                cases a with
                | vals vs st1 =>
                    cases vs with
                    | nil => simp [hC] at h
                    | cons cv vs' =>
                        cases vs' with
                        | cons _ _ => simp [hC] at h
                        | nil =>
                            simp only [hC, Result.ok_bind] at h
                            exact Step.switchExec (ihE _ _ _ _ _ hC) (ihS _ _ _ _ _ _ _ h)
                | halt st1 =>
                    simp [hC] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.switchHalt (ihE _ _ _ _ _ hC)
        | forLoop init c post body =>
            simp only [execStmt] at h
            cases hI : execStmts E n (hoist E.toDialect init :: funs) V st init with
            | stuck => simp [hI] at h
            | outOfFuel => simp [hI] at h
            | ok x =>
                obtain ⟨Vinit, stinit, oinit⟩ := x
                cases oinit with
                | normal =>
                    cases hLp : execLoop E n (hoist E.toDialect init :: funs) Vinit stinit
                        c post body with
                    | stuck => simp [hI, hLp] at h
                    | outOfFuel => simp [hI, hLp] at h
                    | ok y =>
                        obtain ⟨Vend, stend, o2⟩ := y
                        simp [hI, hLp] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact Step.forLoop (ihSS _ _ _ _ _ _ _ hI) (ihL _ _ _ _ _ _ _ _ _ hLp)
                | halt =>
                    simp [hI] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.forInitHalt (ihSS _ _ _ _ _ _ _ hI)
                | «break» => simp [hI] at h
                | «continue» => simp [hI] at h
                | leave => simp [hI] at h
        | «break» =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.«break»
        | «continue» =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.«continue»
        | leave =>
            simp only [execStmt] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.leave
      /- ### Statement sequences -/
      · intro funs V st ss V' st' o h
        cases ss with
        | nil =>
            simp only [execStmts] at h
            injection h with h
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
            exact Step.seqNil
        | cons s rest =>
            simp only [execStmts] at h
            cases hS : execStmt E n funs V st s with
            | stuck => simp [hS] at h
            | outOfFuel => simp [hS] at h
            | ok x =>
                obtain ⟨V1, st1, o1⟩ := x
                cases o1 with
                | normal =>
                    simp only [hS, Result.ok_bind] at h
                    exact Step.seqCons (ihS _ _ _ _ _ _ _ hS) (ihSS _ _ _ _ _ _ _ h)
                | «break» =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
                | «continue» =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
                | leave =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
                | halt =>
                    simp [hS] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact Step.seqStop (ihS _ _ _ _ _ _ _ hS) (by decide)
      /- ### Loop iteration -/
      · intro funs V st c post body V' st' o h
        simp only [execLoop] at h
        cases hC : evalExpr E n funs V st c with
        | stuck => simp [hC] at h
        | outOfFuel => simp [hC] at h
        | ok a =>
            cases a with
            | vals vs st1 =>
                cases vs with
                | nil => simp [hC] at h
                | cons cv vs' =>
                    cases vs' with
                    | cons _ _ => simp [hC] at h
                    | nil =>
                        by_cases hz : cv = E.toDialect.zero
                        · simp [hC, hz] at h
                          obtain ⟨rfl, rfl, rfl⟩ := h
                          exact Step.loopDone (ihE _ _ _ _ _ hC) hz
                        · cases hB : execStmt E n funs V st1 (.block body) with
                          | stuck => simp [hC, hz, hB] at h
                          | outOfFuel => simp [hC, hz, hB] at h
                          | ok x =>
                              obtain ⟨Vb, stb, ob⟩ := x
                              cases ob with
                              | normal =>
                                  cases hP : execStmt E n funs Vb stb (.block post) with
                                  | stuck => simp [hC, hz, hB, hP] at h
                                  | outOfFuel => simp [hC, hz, hB, hP] at h
                                  | ok y =>
                                      obtain ⟨Vp, stp, op⟩ := y
                                      cases op with
                                      | normal =>
                                          simp only [hC, Result.ok_bind] at h
                                          rw [if_neg hz] at h
                                          simp only [hB, Result.ok_bind, hP] at h
                                          exact Step.loopStep (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inl rfl)
                                            (ihS _ _ _ _ _ _ _ hP) (ihL _ _ _ _ _ _ _ _ _ h)
                                      | halt =>
                                          simp [hC, hz, hB, hP] at h
                                          obtain ⟨rfl, rfl, rfl⟩ := h
                                          exact Step.loopPostHalt (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inl rfl)
                                            (ihS _ _ _ _ _ _ _ hP)
                                      | «break» => simp [hC, hz, hB, hP] at h
                                      | «continue» => simp [hC, hz, hB, hP] at h
                                      | leave => simp [hC, hz, hB, hP] at h
                              | «continue» =>
                                  cases hP : execStmt E n funs Vb stb (.block post) with
                                  | stuck => simp [hC, hz, hB, hP] at h
                                  | outOfFuel => simp [hC, hz, hB, hP] at h
                                  | ok y =>
                                      obtain ⟨Vp, stp, op⟩ := y
                                      cases op with
                                      | normal =>
                                          simp only [hC, Result.ok_bind] at h
                                          rw [if_neg hz] at h
                                          simp only [hB, Result.ok_bind, hP] at h
                                          exact Step.loopStep (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inr rfl)
                                            (ihS _ _ _ _ _ _ _ hP) (ihL _ _ _ _ _ _ _ _ _ h)
                                      | halt =>
                                          simp [hC, hz, hB, hP] at h
                                          obtain ⟨rfl, rfl, rfl⟩ := h
                                          exact Step.loopPostHalt (ihE _ _ _ _ _ hC) hz
                                            (ihS _ _ _ _ _ _ _ hB) (Or.inr rfl)
                                            (ihS _ _ _ _ _ _ _ hP)
                                      | «break» => simp [hC, hz, hB, hP] at h
                                      | «continue» => simp [hC, hz, hB, hP] at h
                                      | leave => simp [hC, hz, hB, hP] at h
                              | «break» =>
                                  simp [hC, hz, hB] at h
                                  obtain ⟨rfl, rfl, rfl⟩ := h
                                  exact Step.loopBreak (ihE _ _ _ _ _ hC) hz (ihS _ _ _ _ _ _ _ hB)
                              | leave =>
                                  simp [hC, hz, hB] at h
                                  obtain ⟨rfl, rfl, rfl⟩ := h
                                  exact Step.loopLeave (ihE _ _ _ _ _ hC) hz (ihS _ _ _ _ _ _ _ hB)
                              | halt =>
                                  simp [hC, hz, hB] at h
                                  obtain ⟨rfl, rfl, rfl⟩ := h
                                  exact Step.loopBodyHalt (ihE _ _ _ _ _ hC) hz
                                    (ihS _ _ _ _ _ _ _ hB)
            | halt st1 =>
                simp [hC] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact Step.loopCondHalt (ihE _ _ _ _ _ hC)


/-- A successful whole-program interpreter result yields a relational run
when every computed builtin result is relationally admitted. -/
theorem run_sound_of
    (hE : ∀ op args st result, E.builtinFn op args st = some result →
      E.toDialect.Builtin op args st result)
    {n prog st0 V' st' o}
    (h : Interp.run E n prog st0 = .ok (V', st', o)) :
    Run E.toDialect prog st0 V' st' o :=
  (sound_all_of hE n).2.2.1 _ _ _ _ _ _ _ h

end YulSemantics.Interp
