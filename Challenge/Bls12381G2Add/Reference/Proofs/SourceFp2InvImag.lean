import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvNeg

set_option warningAsError true
/-! # Imaginary component in frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def fp2InvAfterImagReads (yst : EvmState) (out a : U256) : EvmState :=
  let s0 := touchMemory (fp2InvAfterNegReads yst out a) 1696 32
  touchMemory s0 1664 32

def fp2InvImag (yst : EvmState) (out a : U256) : U256 × U256 :=
  let s := fp2InvAfterNegReads yst out a
  fpMulResult (fp2InvAfterImagReads yst out a)
    (fp2InvNeg yst out a).1 (fp2InvNeg yst out a).2
    (loadWord s.memory 1664) (loadWord s.memory 1696)

def fp2InvAfterImagCall (yst : EvmState) (out a : U256) : EvmState :=
  let s := fp2InvAfterNegReads yst out a
  fpMulFinalState (fp2InvAfterImagReads yst out a)
    (fp2InvNeg yst out a).1 (fp2InvNeg yst out a).2
    (loadWord s.memory 1664) (loadWord s.memory 1696)

def fp2InvImagEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00117", (fp2InvImag yst out a).1),
    ("\x00118", (fp2InvImag yst out a).2)] ++ fp2InvInitialEnv out a

def fp2InvAfterImagHigh (yst : EvmState) (out a : U256) : EvmState :=
  mstoreState (fp2InvAfterImagCall yst out a)
    (out + BitVec.ofNat 256 64).toNat (fp2InvImag yst out a).1
def fp2InvFinalState (yst : EvmState) (out a : U256) : EvmState :=
  mstoreState (fp2InvAfterImagHigh yst out a)
    (out + BitVec.ofNat 256 96).toNat (fp2InvImag yst out a).2

private def fp2InvImagCall : Expr Op := .call "\x009"
  [.var "\x00117", .var "\x00118",
    .builtin .mload [.lit (.number 1664)],
    .builtin .mload [.lit (.number 1696)]]

private theorem fp2InvStmt14_shape : fp2InvStmt14 =
    .assign ["\x00117", "\x00118"] fp2InvImagCall := by rfl

private theorem eval_fp2InvImagCall (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvNegEnv yst out a) (fp2InvAfterNegReads yst out a)
      fp2InvImagCall =
    .ok (.vals [(fp2InvImag yst out a).1, (fp2InvImag yst out a).2]
      (fp2InvAfterImagCall yst out a)) := by
  let s := fp2InvAfterNegReads yst out a
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
      (fp2InvNegEnv yst out a) s
      [.var "\x00117", .var "\x00118",
        .builtin .mload [.lit (.number 1664)],
        .builtin .mload [.lit (.number 1696)]] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
      [("ahi", (fp2InvNeg yst out a).1),
        ("alo", (fp2InvNeg yst out a).2),
        ("bhi", loadWord s.memory 1664), ("blo", loadWord s.memory 1696)]
      (fp2InvAfterImagReads yst out a)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterImagReads,
      fp2InvNegEnv, fp2InvInitialEnv, s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue, VEnv.get]
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
    .ok (fp2InvImagEnv yst out a, fp2InvAfterImagCall yst out a, .normal) := by
  rw [fp2InvStmt14_shape, Interp.execStmt, eval_fp2InvImagCall]
  rfl

theorem exec_fp2InvImagStores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvImagEnv yst out a) (fp2InvAfterImagCall yst out a)
      [fp2InvStmt15, fp2InvStmt16] =
    .ok (fp2InvImagEnv yst out a, fp2InvFinalState yst out a,
      .normal) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
