import YulSemantics.Adequacy

set_option warningAsError true

/-!
# Executable Yul interpreter proof bridges

Reusable projections from interpreter computations to the relational big-step
semantics.  Challenge proofs can compute small straight-line fragments without
repeating projections out of `Interp.sound_all`.
-/

namespace Challenge.YulProof.Interpreter

open YulSemantics

variable {E : ExecDialect} [DecidableEq E.toDialect.Value]

theorem evalExpr_of_interp (hE : E.Lawful) {fuel : Nat}
    {funs : FunEnv E.toDialect} {V : VEnv E.toDialect} {st : E.toDialect.State}
    {e : Expr E.toDialect.Op} {result}
    (h : Interp.evalExpr E fuel funs V st e = .ok result) :
    EvalExpr E.toDialect funs V st e result :=
  (Interp.sound_all hE fuel).1 _ _ _ _ _ h

theorem evalArgs_of_interp (hE : E.Lawful) {fuel : Nat}
    {funs : FunEnv E.toDialect} {V : VEnv E.toDialect} {st : E.toDialect.State}
    {args : List (Expr E.toDialect.Op)} {result}
    (h : Interp.evalArgs E fuel funs V st args = .ok result) :
    EvalArgs E.toDialect funs V st args result :=
  (Interp.sound_all hE fuel).2.1 _ _ _ _ _ h

theorem execStmt_of_interp (hE : E.Lawful) {fuel : Nat}
    {funs : FunEnv E.toDialect} {V V' : VEnv E.toDialect}
    {st st' : E.toDialect.State} {stmt : Stmt E.toDialect.Op} {outcome}
    (h : Interp.execStmt E fuel funs V st stmt = .ok (V', st', outcome)) :
    ExecStmt E.toDialect funs V st stmt V' st' outcome :=
  (Interp.sound_all hE fuel).2.2.1 _ _ _ _ _ _ _ h

theorem execStmts_of_interp (hE : E.Lawful) {fuel : Nat}
    {funs : FunEnv E.toDialect} {V V' : VEnv E.toDialect}
    {st st' : E.toDialect.State} {stmts : Block E.toDialect.Op} {outcome}
    (h : Interp.execStmts E fuel funs V st stmts = .ok (V', st', outcome)) :
    ExecStmts E.toDialect funs V st stmts V' st' outcome :=
  (Interp.sound_all hE fuel).2.2.2.1 _ _ _ _ _ _ _ h

theorem execLoop_of_interp (hE : E.Lawful) {fuel : Nat}
    {funs : FunEnv E.toDialect} {V V' : VEnv E.toDialect}
    {st st' : E.toDialect.State} {cond : Expr E.toDialect.Op}
    {post body : Block E.toDialect.Op} {outcome}
    (h : Interp.execLoop E fuel funs V st cond post body = .ok (V', st', outcome)) :
    ExecLoop E.toDialect funs V st cond post body V' st' outcome :=
  (Interp.sound_all hE fuel).2.2.2.2 _ _ _ _ _ _ _ _ _ h

theorem evalBuiltin (hE : E.Lawful) {funs : FunEnv E.toDialect}
    {V : VEnv E.toDialect} {st st1 st2 : E.toDialect.State}
    {op : E.toDialect.Op} {args : List (Expr E.toDialect.Op)} {values returns}
    (hargs : EvalArgs E.toDialect funs V st args (.vals values st1))
    (hfn : E.builtinFn op values st1 = some (.ok returns st2)) :
    EvalExpr E.toDialect funs V st (.builtin op args) (.vals returns st2) :=
  Step.builtinOk hargs ((hE op values st1 (.ok returns st2)).mpr hfn)

end Challenge.YulProof.Interpreter
