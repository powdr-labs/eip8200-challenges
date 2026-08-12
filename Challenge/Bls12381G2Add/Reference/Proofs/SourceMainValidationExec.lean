import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainValidationAnd

set_option warningAsError true

/-! # Frozen G2ADD main point-validity execution -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainValidationStmt_shape : mainValidationStmt =
    .cond (.builtin .iszero [mainValidationAndExpr])
      [.exprStmt (.builtin .invalid [])] := by rfl

private theorem eval_mainValidationCondition (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 72 mainFuns []
      (mainDecodedState yst)
      (.builtin .iszero [mainValidationAndExpr]) =
    .ok (.vals [b2w (mainValidationValue yst = 0)]
      (mainAfterValidationReads yst)) := by
  rw [Interp.evalExpr, Interp.evalArgs, Interp.evalArgs]
  simp
  rw [eval_mainValidationAnd]
  simp [Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, un,
    mainValidationValue, b2w]

private theorem exec_invalidBlock (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 72 mainFuns [] yst
      (.block [.exprStmt (.builtin .invalid [])]) =
      .ok ([], mainInvalidState yst, .halt) := by
  simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr,
    Interp.evalArgs, mainInvalidState, Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, restore]

theorem exec_mainValidation (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 73 mainFuns []
      (mainDecodedState yst) mainValidationStmt =
      if mainValidationValue yst = 0 then
        .ok ([], mainInvalidState (mainAfterValidationReads yst), .halt)
      else .ok ([], mainAfterValidationReads yst, .normal) := by
  rw [mainValidationStmt_shape, Interp.execStmt,
    eval_mainValidationCondition]
  by_cases hvalid : mainValidationValue yst = 0
  · have hb : b2w (mainValidationValue yst = 0) = (1 : U256) := by
      simp [hvalid, b2w]
    rw [if_pos hvalid, hb]
    change (if (1 : U256) =
        Dialect.zero Challenge.EvmProof.modexpExec.toDialect then
      .ok ([], mainAfterValidationReads yst, .normal)
    else Interp.execStmt Challenge.EvmProof.modexpExec 72 mainFuns []
      (mainAfterValidationReads yst)
      (.block [.exprStmt (.builtin .invalid [])])) = _
    rw [if_neg (by decide : (1 : U256) ≠
      Dialect.zero Challenge.EvmProof.modexpExec.toDialect)]
    exact exec_invalidBlock _
  · have hb : b2w (mainValidationValue yst = 0) = (0 : U256) := by
      simp only [b2w]
      rw [if_neg (by simpa using hvalid)]
    rw [if_neg (by simpa using hvalid), hb]
    change (if (0 : U256) =
        Dialect.zero Challenge.EvmProof.modexpExec.toDialect then
      .ok ([], mainAfterValidationReads yst, .normal)
    else Interp.execStmt Challenge.EvmProof.modexpExec 72 mainFuns []
      (mainAfterValidationReads yst)
      (.block [.exprStmt (.builtin .invalid [])])) = _
    rw [if_pos (by rfl : (0 : U256) =
      Dialect.zero Challenge.EvmProof.modexpExec.toDialect)]

theorem exec_mainValidation_success (yst : EvmState)
    (hvalid : mainValidationValue yst ≠ 0) :
    Interp.execStmt Challenge.EvmProof.modexpExec 73 mainFuns []
      (mainDecodedState yst) mainValidationStmt =
      .ok ([], mainAfterValidationReads yst, .normal) := by
  rw [exec_mainValidation, if_neg hvalid]

theorem exec_mainValidation_reject (yst : EvmState)
    (hvalid : mainValidationValue yst = 0) :
    Interp.execStmt Challenge.EvmProof.modexpExec 73 mainFuns []
      (mainDecodedState yst) mainValidationStmt =
      .ok ([], mainInvalidState (mainAfterValidationReads yst), .halt) := by
  rw [exec_mainValidation, if_pos hvalid]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
