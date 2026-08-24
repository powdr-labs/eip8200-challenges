import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulModulus

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem exec_fpReduceCorrections (product : FullMulValue)
    (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 57 fpReduceBodyFuns
      (fpReduceValueEnv product (fpMulRemainderValue product)) yst
      [fpReduceStmt6, fpReduceStmt7] =
    .ok (fpReduceValueEnv product (fpReduceProductValue product),
      yst, .normal) := by
  exact Interp.execStmts_cons_normal
    (exec_fpReduceCorrection1 product yst)
    (Interp.execStmts_cons_normal (exec_fpReduceCorrection2 product yst) (by rfl))

private theorem exec_fpReduceAfterP (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 58 fpReduceBodyFuns
      (fpReducePEnv product) yst
      [fpReduceStmt5, fpReduceStmt6, fpReduceStmt7] =
    .ok (fpReduceValueEnv product (fpReduceProductValue product),
      yst, .normal) := by
  exact Interp.execStmts_cons_normal (exec_fpReduceRemainder product yst)
    (exec_fpReduceCorrections product yst)

private theorem exec_fpReduceAfterQ (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 60 fpReduceBodyFuns
      (fpReduceQEnv product) yst
      [fpReduceStmt3, fpReduceStmt4, fpReduceStmt5, fpReduceStmt6,
        fpReduceStmt7] =
    .ok (fpReduceValueEnv product (fpReduceProductValue product),
      yst, .normal) := by
  exact Interp.execStmts_append_normal
    (E := Challenge.YulProof.ClosedEvm.exec) (n := 58)
    (funs := fpReduceBodyFuns) (V := fpReduceQEnv product) (st := yst)
    (pre := [fpReduceStmt3, fpReduceStmt4])
    (tail := [fpReduceStmt5, fpReduceStmt6, fpReduceStmt7]) (by omega)
    (exec_fpReducePDecls product yst) (exec_fpReduceAfterP product yst)

private theorem exec_fpReduceAfterDecls (product : FullMulValue)
    (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 61 fpReduceBodyFuns
      (fpReduceQDeclEnv product) yst
      [fpReduceStmt2, fpReduceStmt3, fpReduceStmt4, fpReduceStmt5,
        fpReduceStmt6, fpReduceStmt7] =
    .ok (fpReduceValueEnv product (fpReduceProductValue product),
      yst, .normal) := by
  exact Interp.execStmts_cons_normal (exec_fpReduceQuotient product yst)
    (exec_fpReduceAfterQ product yst)

private theorem exec_fpReduceBodyStmts (product : FullMulValue)
    (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 63 fpReduceBodyFuns
      (fpReduceInitialEnv product) yst fpReduceBody =
    .ok (fpReduceValueEnv product (fpReduceProductValue product),
      yst, .normal) := by
  rw [show fpReduceBody = [fpReduceStmt0, fpReduceStmt1] ++
      [fpReduceStmt2, fpReduceStmt3, fpReduceStmt4, fpReduceStmt5,
        fpReduceStmt6, fpReduceStmt7] by rfl]
  exact Interp.execStmts_append_normal
    (E := Challenge.YulProof.ClosedEvm.exec) (n := 61)
    (funs := fpReduceBodyFuns) (V := fpReduceInitialEnv product) (st := yst)
    (pre := [fpReduceStmt0, fpReduceStmt1])
    (tail := [fpReduceStmt2, fpReduceStmt3, fpReduceStmt4, fpReduceStmt5,
      fpReduceStmt6, fpReduceStmt7]) (by omega)
    (exec_fpReduceDecls product yst) (exec_fpReduceAfterDecls product yst)

theorem exec_fpReduceBody (product : FullMulValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 64 fpReduceFuns
      (fpReduceInitialEnv product) yst (.block fpReduceBody) =
    .ok (fpReduceReturnEnv product (fpReduceProductValue product),
      yst, .normal) := by
  rw [Interp.execStmt]
  change (do
    let (V, st, outcome) ← Interp.execStmts Challenge.YulProof.ClosedEvm.exec 63
      fpReduceBodyFuns (fpReduceInitialEnv product) yst fpReduceBody
    return (restore (fpReduceInitialEnv product) V, st, outcome)) = _
  rw [exec_fpReduceBodyStmts product yst]
  change Result.ok (restore (fpReduceInitialEnv product)
    (fpReduceValueEnv product (fpReduceProductValue product)), yst,
      Outcome.normal) = _
  rw [restore_fpReduceValueEnv]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
