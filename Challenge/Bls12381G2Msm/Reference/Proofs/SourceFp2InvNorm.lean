import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvSquare1

set_option warningAsError true

/-! Norm addition in frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2InvAfterNormReads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterNormReads
abbrev fp2InvNorm :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvNorm

def fp2InvNormEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00123", (fp2InvNorm yst a).1),
    ("\x00124", (fp2InvNorm yst a).2)] ++ fp2InvInitialEnv out a

private def fp2InvNormCall : Expr Op := .call "\x004"
  [.builtin .mload [.lit (.number 1536)],
    .builtin .mload [.lit (.number 1568)],
    .builtin .mload [.lit (.number 1600)],
    .builtin .mload [.lit (.number 1632)]]

private theorem fp2InvStmt6_shape : fp2InvStmt6 =
    .assign ["\x00123", "\x00124"] fp2InvNormCall := by rfl

private theorem eval_fp2InvNormCall (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2InvBodyFuns
      (fp2InvSquare1Env yst out a) (fp2InvAfterSquare1Stores yst a)
      fp2InvNormCall =
    .ok (.vals [(fp2InvNorm yst a).1, (fp2InvNorm yst a).2]
      (fp2InvAfterNormReads yst a)) := by
  let s := fp2InvAfterSquare1Stores yst a
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2InvBodyFuns
          (fp2InvSquare1Env yst out a) s
          [.builtin .mload [.lit (.number 1536)],
            .builtin .mload [.lit (.number 1568)],
            .builtin .mload [.lit (.number 1600)],
            .builtin .mload [.lit (.number 1632)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
          [("ahi", loadWord s.memory 1536), ("alo", loadWord s.memory 1568),
            ("bhi", loadWord s.memory 1600), ("blo", loadWord s.memory 1632)]
          (fp2InvAfterNormReads yst a)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterNormReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterNormReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2InvBodyFuns "\x004" =
      lookupFun fp2Funs "\x004" := by rfl
  rw [fp2InvNormCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup]
  rw [show fp2Funs = fpAddFuns by rfl, eval_fpAdd]
  rfl

theorem exec_fp2InvStmt6 (yst : EvmState) (out a : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2InvBodyFuns
      (fp2InvSquare1Env yst out a) (fp2InvAfterSquare1Stores yst a)
      fp2InvStmt6 =
    .ok (fp2InvNormEnv yst out a, fp2InvAfterNormReads yst a, .normal) := by
  rw [fp2InvStmt6_shape, Interp.execStmt, eval_fp2InvNormCall]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
