import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulResult
import Challenge.YulProof.Interpreter

set_option warningAsError true

/-! # Generic relational source-call interface for local `fpMul` -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.YulProof.Interpreter

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpMulDecl : FDecl D :=
  { params := ["\x0071", "\x0072", "\x0073", "\x0074"]
    rets := ["\x0075", "\x0076"]
    body := fpMulBody }

/-- Any caller whose function environment resolves `fpMul` to the frozen
declaration may use the already-proved concrete source body as an opaque call. -/
theorem step_fpMul_call {callerFuns : FunEnv D} {V : VEnv D}
    {args : List (Expr Op)} {yst argsState : EvmState}
    (ahi alo bhi blo : U256)
    (hlookup : lookupFun callerFuns "\x009" = some (fpMulDecl, fpMulFuns))
    (hargs : EvalArgs D callerFuns V yst args
      (.vals [ahi, alo, bhi, blo] argsState)) :
    EvalExpr D callerFuns V yst (.call "\x009" args)
      (.vals [(fpMulResult argsState ahi alo bhi blo).1,
        (fpMulResult argsState ahi alo bhi blo).2] argsState) := by
  have hbody := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (exec_fpMulBody ahi alo bhi blo argsState)
  have hcall := Step.callOk hargs hlookup (by rfl) hbody (Or.inl rfl)
  change EvalExpr D callerFuns V yst (.call "\x009" args)
    (.vals
      [(VEnv.get (fpMulSourceBodyResultEnv ahi alo bhi blo) "\x0075").getD 0,
       (VEnv.get (fpMulSourceBodyResultEnv ahi alo bhi blo) "\x0076").getD 0]
      argsState) at hcall
  rw [fpMulSourceBodyResultEnv_hi, fpMulSourceBodyResultEnv_lo] at hcall
  exact hcall

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
