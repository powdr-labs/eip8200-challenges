import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvNorm

set_option warningAsError true
/-! # Scalar inversion in frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def fp2InvScalar (yst : EvmState) (a : U256) : U256 × U256 :=
  fpInvResult (fp2InvAfterNormReads yst a)
    (fp2InvNorm yst a).1 (fp2InvNorm yst a).2

def fp2InvAfterScalarCall (yst : EvmState) (a : U256) : EvmState :=
  fpInvFinalState (fp2InvAfterNormReads yst a)
    (fp2InvNorm yst a).1 (fp2InvNorm yst a).2

def fp2InvScalarEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00117", (fp2InvScalar yst a).1),
    ("\x00118", (fp2InvScalar yst a).2)] ++ fp2InvInitialEnv out a

def fp2InvAfterScalarHigh (yst : EvmState) (a : U256) : EvmState :=
  mstoreState (fp2InvAfterScalarCall yst a) 1664 (fp2InvScalar yst a).1
def fp2InvAfterScalarStores (yst : EvmState) (a : U256) : EvmState :=
  mstoreState (fp2InvAfterScalarHigh yst a) 1696 (fp2InvScalar yst a).2

private def fp2InvScalarCall : Expr Op := .call "\x0010"
  [.var "\x00117", .var "\x00118"]

private theorem fp2InvStmt7_shape : fp2InvStmt7 =
    .assign ["\x00117", "\x00118"] fp2InvScalarCall := by rfl

private theorem eval_fp2InvScalarCall (yst : EvmState) (out a : U256)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvNormEnv yst out a) (fp2InvAfterNormReads yst a)
      fp2InvScalarCall =
    .ok (.vals [(fp2InvScalar yst a).1, (fp2InvScalar yst a).2]
      (fp2InvAfterScalarCall yst a)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
      (fp2InvNormEnv yst out a) (fp2InvAfterNormReads yst a)
      [.var "\x00117", .var "\x00118"] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpInvFuns
      [("hi", (fp2InvNorm yst a).1), ("lo", (fp2InvNorm yst a).2)]
      (fp2InvAfterNormReads yst a) [.var "hi", .var "lo"] := by
    rfl
  have hlookup : lookupFun fp2InvBodyFuns "\x0010" =
      lookupFun fpInvFuns "\x0010" := by rfl
  rw [fp2InvScalarCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0010") hargs hlookup]
  rw [show fpInvFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl,
    eval_fpInv _ _ _ hhi]
  rfl

theorem exec_fp2InvStmt7 (yst : EvmState) (out a : U256)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2InvBodyFuns
      (fp2InvNormEnv yst out a) (fp2InvAfterNormReads yst a)
      fp2InvStmt7 =
    .ok (fp2InvScalarEnv yst out a, fp2InvAfterScalarCall yst a, .normal) := by
  rw [fp2InvStmt7_shape, Interp.execStmt, eval_fp2InvScalarCall yst out a hhi]
  rfl

theorem exec_fp2InvScalarStores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvScalarEnv yst out a) (fp2InvAfterScalarCall yst a)
      [fp2InvStmt8, fp2InvStmt9] =
    .ok (fp2InvScalarEnv yst out a, fp2InvAfterScalarStores yst a,
      .normal) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
