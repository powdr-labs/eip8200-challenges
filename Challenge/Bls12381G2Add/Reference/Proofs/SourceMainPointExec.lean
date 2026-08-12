import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointDefs

set_option warningAsError true

/-! # Frozen G2ADD point-scope infinity predicate execution -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem eval_mainPointZero (point : Nat)
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns V yst
      (.call "\x0021" [.lit (.number point)]) =
    .ok (.vals [pointZeroValue yst (BitVec.ofNat 256 point)]
      (pointZeroReadState yst (BitVec.ofNat 256 point))) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns V yst
          [.lit (.number point)] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
          [("point", BitVec.ofNat 256 point)] yst [.var "point"] := by
    simp [Interp.evalArgs, Interp.evalExpr, Challenge.EvmProof.modexpExec,
      EVM.litValue, VEnv.get]
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0021") hargs (by rfl)]
  exact eval_pointZero (BitVec.ofNat 256 point) yst

private theorem mainPointStmt0_shape : mainPointStmt0 =
    .letDecl ["\x00131"]
      (some (.call "\x0021" [.lit (.number 0)])) := by rfl

theorem exec_mainInf1 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 mainFuns []
      (mainAfterValidationReads yst) mainPointStmt0 =
    .ok ([("\x00131", mainInf1 yst)], mainAfterInf1Reads yst,
      .normal) := by
  rw [mainPointStmt0_shape, Interp.execStmt,
    eval_mainPointZero 0 []]
  simp [mainInf1, mainAfterInf1Reads]

private theorem mainPointStmt1_shape : mainPointStmt1 =
    .letDecl ["\x00132"]
      (some (.call "\x0021" [.lit (.number 256)])) := by rfl

theorem exec_mainInf2 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 mainFuns
      [("\x00131", mainInf1 yst)] (mainAfterInf1Reads yst)
      mainPointStmt1 =
    .ok (mainPointEnv yst, mainAfterInf2Reads yst, .normal) := by
  rw [mainPointStmt1_shape, Interp.execStmt,
    eval_mainPointZero 256 [("\x00131", mainInf1 yst)]]
  simp [mainInf2, mainAfterInf2Reads, mainPointEnv]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
