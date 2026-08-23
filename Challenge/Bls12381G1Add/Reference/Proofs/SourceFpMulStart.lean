import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulExecDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Staged entry into the frozen G1ADD `fpMul` helper -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem eval_fpMul_args (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] =
    .ok (.vals [ahi, alo, bhi, blo] yst) := by
  rfl

/-- Once the isolated function body is evaluated, the outer function-call
expression returns its two declared result bindings. -/
theorem eval_fpMul_of_body (ahi alo bhi blo : U256) (yst final : EvmState)
    (Vend : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hbody : Interp.execStmt Challenge.EvmProof.modexpExec 67 fpMulFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody) =
        .ok (Vend, final, .normal)) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fpMulFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals
      [(VEnv.get Vend "\x0072").getD 0, (VEnv.get Vend "\x0073").getD 0]
      final) := by
  exact Interp.evalExpr_call_normal
    (eval_fpMul_args ahi alo bhi blo yst) lookup_fpMul (by rfl) hbody

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
