import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainValidationCall1

set_option warningAsError true

/-! # Point-validity conjunction in frozen G2ADD main -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainValidationAndExpr : Expr Op :=
  .builtin .and [.call "\x0020" [.lit (.number 0)],
    .call "\x0020" [.lit (.number 256)]]

theorem eval_mainValidationAnd (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 70 mainFuns []
      (mainDecodedState yst) mainValidationAndExpr =
    .ok (.vals [mainValidationValue yst] (mainAfterValidationReads yst)) := by
  rw [mainValidationAndExpr, Interp.evalExpr]
  simp only [Interp.evalArgs]
  simp
  rw [eval_mainPoint2Valid]
  simp
  rw [eval_mainPoint1Valid_after]
  simp [Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin,
    mainValidationValue]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
