import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainValidationCall2

set_option warningAsError true

/-! # Right-to-left first point-validity call in frozen G2ADD main -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_mainPoint1Valid_after (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns []
      (mainAfterPoint2Valid yst) (.call "\x0020" [.lit (.number 0)]) =
    .ok (.vals [mainPoint1Valid yst] (mainAfterValidationReads yst)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns []
          (mainAfterPoint2Valid yst) [.lit (.number 0)] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
          [("point", (0 : U256))] (mainAfterPoint2Valid yst)
          [.var "point"] := by rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0020") hargs (by rfl)]
  exact eval_pointValid _ _

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
