import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainDecodeExec

set_option warningAsError true

/-! # Right-to-left second point-validity call in frozen G2ADD main -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_mainPoint2Valid (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 67 mainFuns []
      (mainDecodedState yst) (.call "\x0020" [.lit (.number 256)]) =
    .ok (.vals [mainPoint2Valid yst] (mainAfterPoint2Valid yst)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 66 mainFuns []
          (mainDecodedState yst) [.lit (.number 256)] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 66 fp2Funs
          [("point", (256 : U256))] (mainDecodedState yst)
          [.var "point"] := by rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0020") hargs (by rfl)]
  exact eval_pointValid67 _ _

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
