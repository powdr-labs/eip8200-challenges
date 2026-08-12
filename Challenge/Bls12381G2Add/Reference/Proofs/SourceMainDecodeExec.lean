import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainDefs

set_option warningAsError true

/-! # Frozen G2ADD main length and calldata decode execution -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem exec_mainLength_success (yst : EvmState)
    (hsize : yst.env.calldata.length = 512) :
    Interp.execStmt Challenge.EvmProof.modexpExec 16 mainFuns [] yst
      mainLengthStmt = .ok ([], yst, .normal) := by
  simp [mainLengthStmt, Compilation.referenceCompiledBlock,
    Compilation.frozenReferenceBlock, Interp.execStmt, Interp.execStmts,
    Interp.evalExpr, Interp.evalArgs, Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, un, rd0,
    EVM.litValue, b2w, Dialect.zero, hsize]

theorem exec_mainLength_reject (yst : EvmState)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ 512) :
    Interp.execStmt Challenge.EvmProof.modexpExec 16 mainFuns [] yst
      mainLengthStmt = .ok ([], mainInvalidState yst, .halt) := by
  simp [mainLengthStmt, Compilation.referenceCompiledBlock,
    Compilation.frozenReferenceBlock, Interp.execStmt, Interp.execStmts,
    Interp.evalExpr, Interp.evalArgs, Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, un, rd0,
    EVM.litValue, b2w, Dialect.zero, mainInvalidState, restore]
  intro h
  apply hsize
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hn
  rw [Nat.mod_eq_of_lt hfit] at hn
  norm_num at hn
  exact hn

theorem exec_mainStores0 (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 24 mainFuns [] yst
      [mainStore0, mainStore1, mainStore2, mainStore3] =
    .ok ([], mainDecodedState4 yst, .normal) := by
  rfl

theorem exec_mainStores1 (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 24 mainFuns []
      (mainDecodedState4 yst)
      [mainStore4, mainStore5, mainStore6, mainStore7] =
    .ok ([], mainDecodedState8 yst, .normal) := by
  rfl

theorem exec_mainStores2 (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 24 mainFuns []
      (mainDecodedState8 yst)
      [mainStore8, mainStore9, mainStore10, mainStore11] =
    .ok ([], mainDecodedState12 yst, .normal) := by
  rfl

theorem exec_mainStores3 (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 24 mainFuns []
      (mainDecodedState12 yst)
      [mainStore12, mainStore13, mainStore14, mainStore15] =
    .ok ([], mainDecodedState yst, .normal) := by
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
