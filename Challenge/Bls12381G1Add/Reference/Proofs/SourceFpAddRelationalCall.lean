import Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
import Challenge.YulProof.Interpreter
import YulSemantics.Determinism

set_option warningAsError true

/-! # Generic relational source-call interface for `fpAdd` -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.YulProof.Interpreter

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpAddFuns : FunEnv D :=
  [hoist D Compilation.referenceCompiledBlock]

/-- Transport the verified frozen `fpAdd` body to any caller that resolves the
same declaration.  Its internal execution proof is extracted once from the
existing source interpreter theorem and remains opaque to callers. -/
theorem step_fpAdd_call {callerFuns : FunEnv D} {V : VEnv D}
    {args : List (Expr Op)} {yst argsState : EvmState}
    (ahi alo bhi blo : U256)
    (hlookup : lookupFun callerFuns "\x004" = lookupFun fpAddFuns "\x004")
    (hargs : EvalArgs D callerFuns V yst args
      (.vals [ahi, alo, bhi, blo] argsState)) :
    EvalExpr D callerFuns V yst (.call "\x004" args)
      (.vals [(fpAddValue ahi alo bhi blo).1,
        (fpAddValue ahi alo bhi blo).2] argsState) := by
  have href := evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (eval_fpAdd ahi alo bhi blo argsState)
  have hrefArgs : EvalArgs D fpAddFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] argsState
      [.var "ahi", .var "alo", .var "bhi", .var "blo"]
      (.vals [ahi, alo, bhi, blo] argsState) :=
    Step.argsCons (Step.argsCons (Step.argsCons
      (Step.argsCons Step.argsNil (Step.var (by rfl)))
      (Step.var (by rfl))) (Step.var (by rfl))) (Step.var (by rfl))
  generalize hresult :
    (EResult.vals (D := D) [(fpAddValue ahi alo bhi blo).1,
      (fpAddValue ahi alo bhi blo).2] argsState) = result at href
  cases href with
  | callOk hrefArgs' hlookupRef hlen hbody hout =>
      have heq := Step.det
        (fun op => Challenge.YulProof.ClosedEvm.exec_lawful.deterministic op)
        hrefArgs hrefArgs'
      injection heq with heres
      injection heres with hvals hstate
      cases hvals
      cases hstate
      have hcall := Step.callOk hargs (hlookup.trans hlookupRef) hlen hbody hout
      exact hcall
  | callHalt _ _ _ _ => cases hresult
  | callArgsHalt _ => cases hresult

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
