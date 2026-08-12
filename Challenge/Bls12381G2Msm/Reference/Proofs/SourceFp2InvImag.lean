import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvNeg

set_option warningAsError true

/-! Imaginary component and output stores in frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2InvAfterImagReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagReads
abbrev fp2InvImag :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvImag
abbrev fp2InvAfterImagCall :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagCall
abbrev fp2InvAfterImagHigh :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagHigh
abbrev fp2InvFinalState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvFinalState

def fp2InvImagEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00123", (fp2InvImag yst out a).1),
    ("\x00124", (fp2InvImag yst out a).2)] ++ fp2InvInitialEnv out a

private def fp2InvImagCall : Expr Op := .call "\x009"
  [.var "\x00123", .var "\x00124",
    .builtin .mload [.lit (.number 1664)],
    .builtin .mload [.lit (.number 1696)]]

private theorem fp2InvStmt14_shape : fp2InvStmt14 =
    .assign ["\x00123", "\x00124"] fp2InvImagCall := by rfl

private theorem eval_fp2InvImagCall (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvNegEnv yst out a) (fp2InvAfterNegReads yst out a)
      fp2InvImagCall =
    .ok (.vals [(fp2InvImag yst out a).1, (fp2InvImag yst out a).2]
      (fp2InvAfterImagCall yst out a)) := by
  let s := fp2InvAfterNegReads yst out a
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
          (fp2InvNegEnv yst out a) s
          [.var "\x00123", .var "\x00124",
            .builtin .mload [.lit (.number 1664)],
            .builtin .mload [.lit (.number 1696)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", (fp2InvNeg yst out a).1),
            ("alo", (fp2InvNeg yst out a).2),
            ("bhi", loadWord s.memory 1664), ("blo", loadWord s.memory 1696)]
          (fp2InvAfterImagReads yst out a)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterImagReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagReads,
      fp2InvNegEnv, fp2InvInitialEnv, s,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2InvBodyFuns "\x009" =
      lookupFun fpMulFuns "\x009" := by rfl
  rw [fp2InvImagCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup]
  rw [show fpMulFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpMul]
  rfl

theorem exec_fp2InvStmt14 (yst : EvmState) (out a : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2InvBodyFuns
      (fp2InvNegEnv yst out a) (fp2InvAfterNegReads yst out a)
      fp2InvStmt14 =
    .ok (fp2InvImagEnv yst out a, fp2InvAfterImagCall yst out a,
      .normal) := by
  rw [fp2InvStmt14_shape, Interp.execStmt, eval_fp2InvImagCall]
  rfl

theorem exec_fp2InvImagStores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvImagEnv yst out a) (fp2InvAfterImagCall yst out a)
      [fp2InvStmt15, fp2InvStmt16] =
    .ok (fp2InvImagEnv yst out a, fp2InvFinalState yst out a,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
