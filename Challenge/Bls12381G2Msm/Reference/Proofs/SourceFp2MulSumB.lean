import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2MulSumA

set_option warningAsError true

/-! Right component sum in frozen G2MSM `fp2Mul`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2MulAfterSumBReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumBReads
abbrev fp2MulSumB :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulSumB
abbrev fp2MulAfterSumBHigh :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumBHigh
abbrev fp2MulAfterSumBStores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumBStores

def fp2MulSumBEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00119", (fp2MulSumB yst out a b).1),
    ("\x00120", (fp2MulSumB yst out a b).2)] ++ fp2MulInitialEnv out a b

private def fp2MulSumBCall : Expr Op :=
  .call "\x004"
    [.builtin .mload [.var "\x00118"],
      .builtin .mload [.builtin .add [.var "\x00118", .lit (.number 32)]],
      .builtin .mload [.builtin .add [.var "\x00118", .lit (.number 64)]],
      .builtin .mload [.builtin .add [.var "\x00118", .lit (.number 96)]]]

private theorem fp2MulStmt12_shape : fp2MulStmt12 =
    .assign ["\x00119", "\x00120"] fp2MulSumBCall := by rfl

private theorem eval_fp2MulSumBCall (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2MulBodyFuns
      (fp2MulSumAEnv yst out a b) (fp2MulAfterSumAStores yst out a b)
      fp2MulSumBCall =
    .ok (.vals [(fp2MulSumB yst out a b).1, (fp2MulSumB yst out a b).2]
      (fp2MulAfterSumBReads yst out a b)) := by
  let s := fp2MulAfterSumAStores yst out a b
  have hget : VEnv.get (fp2MulSumAEnv yst out a b) "\x00118" = some b := by rfl
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2MulBodyFuns
          (fp2MulSumAEnv yst out a b) s
          [.builtin .mload [.var "\x00118"],
            .builtin .mload [.builtin .add [.var "\x00118", .lit (.number 32)]],
            .builtin .mload [.builtin .add [.var "\x00118", .lit (.number 64)]],
            .builtin .mload [.builtin .add [.var "\x00118", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
          [("ahi", loadWord s.memory b.toNat),
            ("alo", loadWord s.memory (b + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord s.memory (b + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (b + BitVec.ofNat 256 96).toNat)]
          (fp2MulAfterSumBReads yst out a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterSumBReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumBReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      hget, s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, EVM.litValue]
    rfl
  have hlookup : lookupFun fp2MulBodyFuns "\x004" =
      lookupFun fp2Funs "\x004" := by rfl
  rw [fp2MulSumBCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup]
  rw [show fp2Funs = fpAddFuns by rfl, eval_fpAdd]
  rfl

theorem exec_fp2MulStmt12 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2MulBodyFuns
      (fp2MulSumAEnv yst out a b) (fp2MulAfterSumAStores yst out a b)
      fp2MulStmt12 =
    .ok (fp2MulSumBEnv yst out a b, fp2MulAfterSumBReads yst out a b,
      .normal) := by
  rw [fp2MulStmt12_shape, Interp.execStmt, eval_fp2MulSumBCall]
  rfl

theorem exec_fp2MulSumBStores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulSumBEnv yst out a b) (fp2MulAfterSumBReads yst out a b)
      [fp2MulStmt13, fp2MulStmt14] =
    .ok (fp2MulSumBEnv yst out a b, fp2MulAfterSumBStores yst out a b,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
