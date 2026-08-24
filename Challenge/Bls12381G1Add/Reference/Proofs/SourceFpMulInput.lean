import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulInputDefs

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 100000

/-! # Frozen native `fpMul` wrapper reduction call -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpMulSourceAssignedEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  let reduced := fpReduceProductValue (fullMulValue ahi alo bhi blo)
  VEnv.setMany (fpMulProductEnv ahi alo bhi blo) ["\x0075", "\x0076"]
    [reduced.hi, reduced.lo]

private theorem eval_fpReduceProductLocals (ahi alo bhi blo : U256)
    (yst : EvmState) :
    let product := fullMulValue ahi alo bhi blo
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo) yst
      (.call "\x0014" [.var "\x0077", .var "\x0078", .var "\x0079"]) =
    .ok (.vals [(fpReduceProductValue product).hi,
      (fpReduceProductValue product).lo] yst) := by
  intro product
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 fpMulBodyFuns
        (fpMulProductEnv ahi alo bhi blo) yst
        [.var "\x0077", .var "\x0078", .var "\x0079"] =
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 fpReduceFuns
        [("r2", product.r2), ("r1", product.r1), ("r0", product.r0)] yst
        [.var "r2", .var "r1", .var "r0"] := by
    rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x0014") hargs
    (show lookupFun fpMulBodyFuns "\x0014" =
      lookupFun fpReduceFuns "\x0014" by rfl)]
  exact eval_fpReduceProduct product yst

theorem exec_fpMulStmt1 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo) yst fpMulStmt1 =
    .ok (fpMulSourceAssignedEnv ahi alo bhi blo, yst, .normal) := by
  rw [show fpMulStmt1 = .assign ["\x0075", "\x0076"]
      (.call "\x0014" [.var "\x0077", .var "\x0078", .var "\x0079"])
      by rfl]
  simp only [Interp.execStmt.eq_def]
  rw [eval_fpReduceProductLocals]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
