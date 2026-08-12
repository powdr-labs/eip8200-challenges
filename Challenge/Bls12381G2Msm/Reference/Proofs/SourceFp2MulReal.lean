import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2MulPhase1

set_option warningAsError true

/-! Real component of frozen G2MSM `fp2Mul`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2MulAfterRealReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealReads
abbrev fp2MulReal :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulReal
abbrev fp2MulAfterRealHigh :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealHigh
abbrev fp2MulAfterRealStores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealStores

def fp2MulRealEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00119", (fp2MulReal yst a b).1), ("\x00120", (fp2MulReal yst a b).2)] ++
    fp2MulInitialEnv out a b

private def fp2MulRealCall : Expr Op :=
  .call "\x005"
    [.builtin .mload [.lit (.number 1536)],
      .builtin .mload [.lit (.number 1568)],
      .builtin .mload [.lit (.number 1600)],
      .builtin .mload [.lit (.number 1632)]]

private theorem fp2MulStmt6_shape : fp2MulStmt6 =
    .assign ["\x00119", "\x00120"] fp2MulRealCall := by rfl

private theorem eval_fp2MulRealCall (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2MulBodyFuns
      (fp2MulV1Env yst out a b) (fp2MulAfterV1Stores yst a b)
      fp2MulRealCall =
    .ok (.vals [(fp2MulReal yst a b).1, (fp2MulReal yst a b).2]
      (fp2MulAfterRealReads yst a b)) := by
  let s := fp2MulAfterV1Stores yst a b
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2MulBodyFuns
          (fp2MulV1Env yst out a b) s
          [.builtin .mload [.lit (.number 1536)],
            .builtin .mload [.lit (.number 1568)],
            .builtin .mload [.lit (.number 1600)],
            .builtin .mload [.lit (.number 1632)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
          [("ahi", loadWord s.memory 1536), ("alo", loadWord s.memory 1568),
            ("bhi", loadWord s.memory 1600), ("blo", loadWord s.memory 1632)]
          (fp2MulAfterRealReads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterRealReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2MulBodyFuns "\x005" =
      lookupFun fp2Funs "\x005" := by rfl
  rw [fp2MulRealCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x005") hargs hlookup]
  rw [show fp2Funs = fpSubFuns by rfl]
  rw [eval_fpSub]
  rfl

theorem exec_fp2MulStmt6 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2MulBodyFuns
      (fp2MulV1Env yst out a b) (fp2MulAfterV1Stores yst a b)
      fp2MulStmt6 =
    .ok (fp2MulRealEnv yst out a b, fp2MulAfterRealReads yst a b,
      .normal) := by
  rw [fp2MulStmt6_shape, Interp.execStmt, eval_fp2MulRealCall]
  rfl

theorem exec_fp2MulRealStores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulRealEnv yst out a b) (fp2MulAfterRealReads yst a b)
      [fp2MulStmt7, fp2MulStmt8] =
    .ok (fp2MulRealEnv yst out a b, fp2MulAfterRealStores yst out a b,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
