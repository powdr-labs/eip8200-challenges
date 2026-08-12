import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvScalar

set_option warningAsError true

/-! Real component in frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2InvAfterRealReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealReads
abbrev fp2InvReal :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvReal
abbrev fp2InvAfterRealCall :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealCall
abbrev fp2InvAfterRealHigh :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealHigh
abbrev fp2InvAfterRealStores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealStores

def fp2InvRealEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00123", (fp2InvReal yst a).1),
    ("\x00124", (fp2InvReal yst a).2)] ++ fp2InvInitialEnv out a

private def fp2InvRealCall : Expr Op := .call "\x009"
  [.builtin .mload [.var "\x00122"],
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 32)]],
    .builtin .mload [.lit (.number 1664)],
    .builtin .mload [.lit (.number 1696)]]

private theorem fp2InvStmt10_shape : fp2InvStmt10 =
    .assign ["\x00123", "\x00124"] fp2InvRealCall := by rfl

private theorem eval_fp2InvRealCall (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvScalarEnv yst out a) (fp2InvAfterScalarStores yst a)
      fp2InvRealCall =
    .ok (.vals [(fp2InvReal yst a).1, (fp2InvReal yst a).2]
      (fp2InvAfterRealCall yst a)) := by
  let s := fp2InvAfterScalarStores yst a
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
          (fp2InvScalarEnv yst out a) s
          [.builtin .mload [.var "\x00122"],
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 32)]],
            .builtin .mload [.lit (.number 1664)],
            .builtin .mload [.lit (.number 1696)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", loadWord s.memory a.toNat),
            ("alo", loadWord s.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord s.memory 1664), ("blo", loadWord s.memory 1696)]
          (fp2InvAfterRealReads yst a)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterRealReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      fp2InvScalarEnv, fp2InvInitialEnv, s,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2InvBodyFuns "\x009" =
      lookupFun fpMulFuns "\x009" := by rfl
  rw [fp2InvRealCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup]
  rw [show fpMulFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpMul]
  rfl

theorem exec_fp2InvStmt10 (yst : EvmState) (out a : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2InvBodyFuns
      (fp2InvScalarEnv yst out a) (fp2InvAfterScalarStores yst a)
      fp2InvStmt10 =
    .ok (fp2InvRealEnv yst out a, fp2InvAfterRealCall yst a, .normal) := by
  rw [fp2InvStmt10_shape, Interp.execStmt, eval_fp2InvRealCall]
  rfl

theorem exec_fp2InvRealStores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvRealEnv yst out a) (fp2InvAfterRealCall yst a)
      [fp2InvStmt11, fp2InvStmt12] =
    .ok (fp2InvRealEnv yst out a, fp2InvAfterRealStores yst out a,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
