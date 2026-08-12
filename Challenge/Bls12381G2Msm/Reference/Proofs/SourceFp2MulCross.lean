import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2MulSumB

set_option warningAsError true

/-! Cross product in frozen G2MSM `fp2Mul`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2MulAfterCrossReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterCrossReads
abbrev fp2MulCross :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulCross
abbrev fp2MulAfterCrossCall :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterCrossCall
abbrev fp2MulAfterCrossHigh :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterCrossHigh
abbrev fp2MulAfterCrossStores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterCrossStores

def fp2MulCrossEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00119", (fp2MulCross yst out a b).1),
    ("\x00120", (fp2MulCross yst out a b).2)] ++ fp2MulInitialEnv out a b

private def fp2MulCrossCall : Expr Op := .call "\x009"
  [.builtin .mload [.lit (.number 1664)],
    .builtin .mload [.lit (.number 1696)],
    .builtin .mload [.lit (.number 1728)],
    .builtin .mload [.lit (.number 1760)]]

private theorem fp2MulStmt15_shape : fp2MulStmt15 =
    .assign ["\x00119", "\x00120"] fp2MulCrossCall := by rfl

private theorem eval_fp2MulCrossCall (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2MulBodyFuns
      (fp2MulSumBEnv yst out a b) (fp2MulAfterSumBStores yst out a b)
      fp2MulCrossCall =
    .ok (.vals [(fp2MulCross yst out a b).1, (fp2MulCross yst out a b).2]
      (fp2MulAfterCrossCall yst out a b)) := by
  let s := fp2MulAfterSumBStores yst out a b
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2MulBodyFuns
          (fp2MulSumBEnv yst out a b) s
          [.builtin .mload [.lit (.number 1664)],
            .builtin .mload [.lit (.number 1696)],
            .builtin .mload [.lit (.number 1728)],
            .builtin .mload [.lit (.number 1760)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", loadWord s.memory 1664), ("alo", loadWord s.memory 1696),
            ("bhi", loadWord s.memory 1728), ("blo", loadWord s.memory 1760)]
          (fp2MulAfterCrossReads yst out a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterCrossReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterCrossReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2MulBodyFuns "\x009" =
      lookupFun fpMulFuns "\x009" := by rfl
  rw [fp2MulCrossCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup]
  rw [show fpMulFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpMul]
  rfl

theorem exec_fp2MulStmt15 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2MulBodyFuns
      (fp2MulSumBEnv yst out a b) (fp2MulAfterSumBStores yst out a b)
      fp2MulStmt15 =
    .ok (fp2MulCrossEnv yst out a b, fp2MulAfterCrossCall yst out a b,
      .normal) := by
  rw [fp2MulStmt15_shape, Interp.execStmt, eval_fp2MulCrossCall]
  rfl

theorem exec_fp2MulCrossStores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulCrossEnv yst out a b) (fp2MulAfterCrossCall yst out a b)
      [fp2MulStmt16, fp2MulStmt17] =
    .ok (fp2MulCrossEnv yst out a b, fp2MulAfterCrossStores yst out a b,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
