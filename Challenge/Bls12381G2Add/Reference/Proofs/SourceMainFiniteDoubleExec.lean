import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFp2Calls

set_option warningAsError true

/-! # Frozen G2ADD finite doubling arithmetic -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainDoubleBody_shape : mainDoubleBody =
    [.exprStmt (.call "\x0016"
      [.lit (.number 2176), .lit (.number 0), .lit (.number 0)]),
     .exprStmt (.call "\x0014"
      [.lit (.number 2304), .lit (.number 2176), .lit (.number 2176)]),
     .exprStmt (.call "\x0014"
      [.lit (.number 2304), .lit (.number 2304), .lit (.number 2176)]),
     .exprStmt (.call "\x0014"
      [.lit (.number 2432), .lit (.number 128), .lit (.number 128)]),
     .exprStmt (.call "\x0017"
      [.lit (.number 2560), .lit (.number 2432)]),
     .exprStmt (.call "\x0016"
      [.lit (.number 2048), .lit (.number 2304), .lit (.number 2560)])] := by rfl

theorem step_mainDoubleBody (yst : EvmState)
    (hinv : (fp2InvNorm (mainDoubleState3 yst) 2432).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterDoubleYZero yst) mainDoubleBody []
      (mainDoubleFinalState yst) .normal := by
  rw [mainDoubleBody_shape]
  exact Step.seqCons (Step.exprStmt (step_fp2MulLiteral [] _ 2176 0 0))
    (Step.seqCons (Step.exprStmt (step_fp2AddLiteral [] _ 2304 2176 2176))
      (Step.seqCons (Step.exprStmt (step_fp2AddLiteral [] _ 2304 2304 2176))
        (Step.seqCons (Step.exprStmt (step_fp2AddLiteral [] _ 2432 128 128))
          (Step.seqCons (Step.exprStmt
            (step_fp2InvLiteral [] _ 2560 2432 hinv))
            (Step.seqCons (Step.exprStmt
              (step_fp2MulLiteral [] _ 2048 2304 2560)) Step.seqNil)))))

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
