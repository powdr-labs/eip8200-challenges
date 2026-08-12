import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvReal

set_option warningAsError true

/-! Imaginary negation in frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2InvAfterNegReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterNegReads
abbrev fp2InvNeg :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvNeg

def fp2InvNegEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00123", (fp2InvNeg yst out a).1),
    ("\x00124", (fp2InvNeg yst out a).2)] ++ fp2InvInitialEnv out a

private def fp2InvNegCall : Expr Op := .call "\x005"
  [.lit (.number 0), .lit (.number 0),
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 64)]],
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 96)]]]

private theorem fp2InvStmt13_shape : fp2InvStmt13 =
    .assign ["\x00123", "\x00124"] fp2InvNegCall := by rfl

private theorem eval_fp2InvNegCall (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2InvBodyFuns
      (fp2InvRealEnv yst out a) (fp2InvAfterRealStores yst out a)
      fp2InvNegCall =
    .ok (.vals [(fp2InvNeg yst out a).1, (fp2InvNeg yst out a).2]
      (fp2InvAfterNegReads yst out a)) := by
  let s := fp2InvAfterRealStores yst out a
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2InvBodyFuns
          (fp2InvRealEnv yst out a) s
          [.lit (.number 0), .lit (.number 0),
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 64)]],
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
          [("ahi", 0), ("alo", 0),
            ("bhi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat)]
          (fp2InvAfterNegReads yst out a)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterNegReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterNegReads,
      fp2InvRealEnv, fp2InvInitialEnv, s,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2InvBodyFuns "\x005" =
      lookupFun fp2Funs "\x005" := by rfl
  rw [fp2InvNegCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x005") hargs hlookup]
  rw [show fp2Funs = fpSubFuns by rfl, eval_fpSub]
  rfl

theorem exec_fp2InvStmt13 (yst : EvmState) (out a : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2InvBodyFuns
      (fp2InvRealEnv yst out a) (fp2InvAfterRealStores yst out a)
      fp2InvStmt13 =
    .ok (fp2InvNegEnv yst out a, fp2InvAfterNegReads yst out a, .normal) := by
  rw [fp2InvStmt13_shape, Interp.execStmt, eval_fp2InvNegCall]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
