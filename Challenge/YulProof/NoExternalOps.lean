import YulSemantics.Ast
import YulSemantics.Dialect.EVMOp

set_option warningAsError true

/-!
# Source-only rejection of external Yul operations

This executable AST predicate recursively checks every expression, nested
block, function body, branch, and loop.  It rejects EVM call and creation
builtins while allowing ordinary local builtins and user-defined function
calls.  It is intentionally independent of execution, compilation, and EVM
bytecode.
-/

namespace Challenge.YulProof.NoExternalOps

open YulSemantics
open YulSemantics.EVM

/-- Builtins which cross an external call or creation boundary. -/
def forbidden : Op → Bool
  | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => true
  | _ => false

mutual

/-- Recursively check one expression. User-function calls are local, but
their arguments must themselves contain no external builtin. Function bodies
are checked at their declaration sites by `stmt`. -/
def expr : Expr Op → Bool
  | .lit _ | .var _ => true
  | .builtin op args => !forbidden op && exprs args
  | .call _ args => exprs args

def exprs : List (Expr Op) → Bool
  | [] => true
  | value :: values => expr value && exprs values

end


mutual

def stmt : Stmt Op → Bool
  | .block body => block body
  | .funDef _ _ _ body => block body
  | .letDecl _ value => value.all expr
  | .assign _ value => expr value
  | .cond condition body => expr condition && block body
  | .switch condition cases fallback =>
      expr condition && caseBlocks cases && fallbackBlock fallback
  | .forLoop init condition post body =>
      block init && expr condition && block post && block body
  | .exprStmt value => expr value
  | .break | .continue | .leave => true
  termination_by statement => 2 * sizeOf statement

def block : Block Op → Bool
  | [] => true
  | statement :: statements => stmt statement && block statements
  termination_by statements => 2 * sizeOf statements + 1

def caseBlocks : List (Literal × Block Op) → Bool
  | [] => true
  | (_, body) :: cases => block body && caseBlocks cases
  termination_by cases => 2 * sizeOf cases + 1

def fallbackBlock : Option (Block Op) → Bool
  | none => true
  | some body => block body
  termination_by fallback => 2 * sizeOf fallback + 1

decreasing_by
  all_goals simp_wf

end

/-- Propositional source predicate backed by the executable recursive check. -/
def Holds (program : Block Op) : Prop := block program = true

instance (program : Block Op) : Decidable (Holds program) :=
  inferInstanceAs (Decidable (block program = true))

/-- An optional parser result is accepted only when parsing succeeded and the
resulting block contains no external operation. -/
def ParsedHolds (program? : Option (Block Op)) : Prop :=
  match program? with
  | some program => Holds program
  | none => False

instance (program? : Option (Block Op)) : Decidable (ParsedHolds program?) := by
  cases program? <;> simp only [ParsedHolds] <;> infer_instance

@[simp] theorem forbidden_call : forbidden .call = true := rfl
@[simp] theorem forbidden_callcode : forbidden .callcode = true := rfl
@[simp] theorem forbidden_delegatecall : forbidden .delegatecall = true := rfl
@[simp] theorem forbidden_staticcall : forbidden .staticcall = true := rfl
@[simp] theorem forbidden_create : forbidden .create = true := rfl
@[simp] theorem forbidden_create2 : forbidden .create2 = true := rfl

theorem ParsedHolds.isSome {program? : Option (Block Op)}
    (h : ParsedHolds program?) : program?.isSome := by
  cases program? <;> simp_all [ParsedHolds]

theorem ParsedHolds.get {program? : Option (Block Op)}
    (h : ParsedHolds program?) : Holds (program?.get h.isSome) := by
  cases program? with
  | none =>
      change False at h
      contradiction
  | some program =>
      change Holds program at h
      exact h

end Challenge.YulProof.NoExternalOps
