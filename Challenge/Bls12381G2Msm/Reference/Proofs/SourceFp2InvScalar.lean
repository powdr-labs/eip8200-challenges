import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvNorm

set_option warningAsError true

/-! Scalar inversion in frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2InvScalar :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvScalar
abbrev fp2InvAfterScalarCall :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterScalarCall
abbrev fp2InvAfterScalarHigh :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterScalarHigh
abbrev fp2InvAfterScalarStores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterScalarStores

def fp2InvScalarEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00123", (fp2InvScalar yst a).1),
    ("\x00124", (fp2InvScalar yst a).2)] ++ fp2InvInitialEnv out a

private def fp2InvScalarCall : Expr Op := .call "\x0010"
  [.var "\x00123", .var "\x00124"]

private theorem fp2InvStmt7_shape : fp2InvStmt7 =
    .assign ["\x00123", "\x00124"] fp2InvScalarCall := by rfl

private theorem eval_fp2InvScalarCall (yst : EvmState) (out a : U256)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvNormEnv yst out a) (fp2InvAfterNormReads yst a)
      fp2InvScalarCall =
    .ok (.vals [(fp2InvScalar yst a).1, (fp2InvScalar yst a).2]
      (fp2InvAfterScalarCall yst a)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
          (fp2InvNormEnv yst out a) (fp2InvAfterNormReads yst a)
          [.var "\x00123", .var "\x00124"] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpInvFuns
          [("hi", (fp2InvNorm yst a).1), ("lo", (fp2InvNorm yst a).2)]
          (fp2InvAfterNormReads yst a) [.var "hi", .var "lo"] := by rfl
  have hlookup : lookupFun fp2InvBodyFuns "\x0010" =
      lookupFun fpInvFuns "\x0010" := by rfl
  rw [fp2InvScalarCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0010") hargs hlookup]
  rw [show fpInvFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpInv _ _ _ hhi]
  rfl

theorem exec_fp2InvStmt7 (yst : EvmState) (out a : U256)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2InvBodyFuns
      (fp2InvNormEnv yst out a) (fp2InvAfterNormReads yst a)
      fp2InvStmt7 =
    .ok (fp2InvScalarEnv yst out a, fp2InvAfterScalarCall yst a,
      .normal) := by
  rw [fp2InvStmt7_shape, Interp.execStmt, eval_fp2InvScalarCall yst out a hhi]
  rfl

theorem exec_fp2InvScalarStores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvScalarEnv yst out a) (fp2InvAfterScalarCall yst a)
      [fp2InvStmt8, fp2InvStmt9] =
    .ok (fp2InvScalarEnv yst out a, fp2InvAfterScalarStores yst a,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
