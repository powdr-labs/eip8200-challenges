import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2MulReal

set_option warningAsError true

/-! Left component sum in frozen G2MSM `fp2Mul`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2MulAfterSumAReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumAReads
abbrev fp2MulSumA :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulSumA
abbrev fp2MulAfterSumAHigh :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumAHigh
abbrev fp2MulAfterSumAStores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumAStores

def fp2MulSumAEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00119", (fp2MulSumA yst out a b).1),
    ("\x00120", (fp2MulSumA yst out a b).2)] ++ fp2MulInitialEnv out a b

private def fp2MulSumACall : Expr Op :=
  .call "\x004"
    [.builtin .mload [.var "\x00117"],
      .builtin .mload [.builtin .add [.var "\x00117", .lit (.number 32)]],
      .builtin .mload [.builtin .add [.var "\x00117", .lit (.number 64)]],
      .builtin .mload [.builtin .add [.var "\x00117", .lit (.number 96)]]]

private theorem fp2MulStmt9_shape : fp2MulStmt9 =
    .assign ["\x00119", "\x00120"] fp2MulSumACall := by rfl

private theorem eval_fp2MulSumACall (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2MulBodyFuns
      (fp2MulRealEnv yst out a b) (fp2MulAfterRealStores yst out a b)
      fp2MulSumACall =
    .ok (.vals [(fp2MulSumA yst out a b).1, (fp2MulSumA yst out a b).2]
      (fp2MulAfterSumAReads yst out a b)) := by
  let s := fp2MulAfterRealStores yst out a b
  have hget : VEnv.get (fp2MulRealEnv yst out a b) "\x00117" = some a := by rfl
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2MulBodyFuns
          (fp2MulRealEnv yst out a b) s
          [.builtin .mload [.var "\x00117"],
            .builtin .mload [.builtin .add [.var "\x00117", .lit (.number 32)]],
            .builtin .mload [.builtin .add [.var "\x00117", .lit (.number 64)]],
            .builtin .mload [.builtin .add [.var "\x00117", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
          [("ahi", loadWord s.memory a.toNat),
            ("alo", loadWord s.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat)]
          (fp2MulAfterSumAReads yst out a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterSumAReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterSumAReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      hget, s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, EVM.litValue]
    rfl
  have hlookup : lookupFun fp2MulBodyFuns "\x004" =
      lookupFun fp2Funs "\x004" := by rfl
  rw [fp2MulSumACall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup]
  rw [show fp2Funs = fpAddFuns by rfl, eval_fpAdd]
  rfl

theorem exec_fp2MulStmt9 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2MulBodyFuns
      (fp2MulRealEnv yst out a b) (fp2MulAfterRealStores yst out a b)
      fp2MulStmt9 =
    .ok (fp2MulSumAEnv yst out a b, fp2MulAfterSumAReads yst out a b,
      .normal) := by
  rw [fp2MulStmt9_shape, Interp.execStmt, eval_fp2MulSumACall]
  rfl

theorem exec_fp2MulSumAStores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulSumAEnv yst out a b) (fp2MulAfterSumAReads yst out a b)
      [fp2MulStmt10, fp2MulStmt11] =
    .ok (fp2MulSumAEnv yst out a b, fp2MulAfterSumAStores yst out a b,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
