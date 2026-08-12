import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDoubleExec

set_option warningAsError true

/-! # Frozen G2ADD unequal-x slope arithmetic -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainUnequalBody_shape : mainUnequalBody =
    [.exprStmt (.call "\x0015"
      [.lit (.number 2304), .lit (.number 384), .lit (.number 128)]),
     .exprStmt (.call "\x0015"
      [.lit (.number 2432), .lit (.number 256), .lit (.number 0)]),
     .exprStmt (.call "\x0017"
      [.lit (.number 2560), .lit (.number 2432)]),
     .exprStmt (.call "\x0016"
      [.lit (.number 2048), .lit (.number 2304), .lit (.number 2560)])] := by rfl

theorem step_mainUnequalBody (yst : EvmState)
    (hinv : (fp2InvNorm (mainUnequalState1 yst) 2432).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq2 yst) mainUnequalBody []
      (mainUnequalFinalState yst) .normal := by
  rw [mainUnequalBody_shape]
  exact Step.seqCons (Step.exprStmt (step_fp2SubLiteral [] _ 2304 384 128))
    (Step.seqCons (Step.exprStmt (step_fp2SubLiteral [] _ 2432 256 0))
      (Step.seqCons (Step.exprStmt
        (step_fp2InvLiteral [] _ 2560 2432 hinv))
        (Step.seqCons (Step.exprStmt
          (step_fp2MulLiteral [] _ 2048 2304 2560)) Step.seqNil)))

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
