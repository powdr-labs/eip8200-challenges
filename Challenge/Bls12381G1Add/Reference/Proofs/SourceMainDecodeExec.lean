import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainValidationDefs

set_option warningAsError true

/-! # Frozen G1ADD main decode execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem exec_mainLength_success (yst : EvmState)
    (hsize : yst.env.calldata.length = 256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 16 mainFuns [] yst
      mainLengthStmt = .ok ([], yst, .normal) := by
  simp [mainLengthStmt, Compilation.referenceCompiledBlock,
    Compilation.frozenReferenceBlock, Interp.execStmt, Interp.execStmts,
    Interp.evalExpr, Interp.evalArgs, Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, un, rd0,
    EVM.litValue, b2w, Dialect.zero, hsize]

theorem exec_mainStores (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 32 mainFuns [] yst
      [mainStore0, mainStore1, mainStore2, mainStore3,
        mainStore4, mainStore5, mainStore6, mainStore7] =
    .ok ([], mainDecodedState yst, .normal) := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
