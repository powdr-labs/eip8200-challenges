import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulCall

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem eval_fpReduceProductReturned (product : FullMulValue)
    (yst : EvmState) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65 fpReduceFuns
      [("r2", product.r2), ("r1", product.r1), ("r0", product.r0)] yst
      (.call "\x0014" [.var "r2", .var "r1", .var "r0"]) =
    .ok (.vals [
      (VEnv.get (fpReduceReturnEnv product (fpReduceProductValue product))
        "\x00136").getD 0,
      (VEnv.get (fpReduceReturnEnv product (fpReduceProductValue product))
        "\x00137").getD 0] yst) := by
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 fpReduceFuns
        [("r2", product.r2), ("r1", product.r1), ("r0", product.r0)] yst
        [.var "r2", .var "r1", .var "r0"] =
      .ok (.vals [product.r2, product.r1, product.r0] yst) := by rfl
  have hlookup : lookupFun fpReduceFuns "\x0014" = some
      ({ params := ["\x00133", "\x00134", "\x00135"]
         rets := ["\x00136", "\x00137"]
         body := fpReduceBody }, fpReduceFuns) := by rfl
  have h := Interp.evalExpr_call_normal hargs hlookup (by rfl)
    (exec_fpReduceBody product yst)
  exact h

/-- The normalized local Barrett helper returns its exact source-word graph. -/
theorem eval_fpReduceProduct (product : FullMulValue) (yst : EvmState) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65 fpReduceFuns
      [("r2", product.r2), ("r1", product.r1), ("r0", product.r0)] yst
      (.call "\x0014" [.var "r2", .var "r1", .var "r0"]) =
    .ok (.vals [(fpReduceProductValue product).hi,
      (fpReduceProductValue product).lo] yst) := by
  calc
    _ = .ok (.vals [
        (VEnv.get (fpReduceReturnEnv product (fpReduceProductValue product))
          "\x00136").getD 0,
        (VEnv.get (fpReduceReturnEnv product (fpReduceProductValue product))
          "\x00137").getD 0] yst) :=
      eval_fpReduceProductReturned product yst
    _ = _ := congrArg (fun values : List U256 =>
      (Result.ok (EResult.vals values yst) :
        Result (EResult Challenge.YulProof.ClosedEvm.dialect)))
      (fpReduceReturn_values product (fpReduceProductValue product))

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
