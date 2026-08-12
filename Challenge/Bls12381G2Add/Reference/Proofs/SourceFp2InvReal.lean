import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvScalar

set_option warningAsError true
/-! # Real component in frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def fp2InvAfterRealReads (yst : EvmState) (a : U256) : EvmState :=
  fp2AddReadState (fp2InvAfterScalarStores yst a)
    a (a + BitVec.ofNat 256 32)
    (BitVec.ofNat 256 1664) (BitVec.ofNat 256 1696)

def fp2InvReal (yst : EvmState) (a : U256) : U256 × U256 :=
  let s := fp2InvAfterScalarStores yst a
  fpMulResult (fp2InvAfterRealReads yst a)
    (loadWord s.memory a.toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord s.memory 1664) (loadWord s.memory 1696)

def fp2InvAfterRealCall (yst : EvmState) (a : U256) : EvmState :=
  let s := fp2InvAfterScalarStores yst a
  fpMulFinalState (fp2InvAfterRealReads yst a)
    (loadWord s.memory a.toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord s.memory 1664) (loadWord s.memory 1696)

def fp2InvRealEnv (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00117", (fp2InvReal yst a).1),
    ("\x00118", (fp2InvReal yst a).2)] ++ fp2InvInitialEnv out a

def fp2InvAfterRealHigh (yst : EvmState) (out a : U256) : EvmState :=
  mstoreState (fp2InvAfterRealCall yst a) out.toNat (fp2InvReal yst a).1
def fp2InvAfterRealStores (yst : EvmState) (out a : U256) : EvmState :=
  mstoreState (fp2InvAfterRealHigh yst out a)
    (out + BitVec.ofNat 256 32).toNat (fp2InvReal yst a).2

private def fp2InvRealCall : Expr Op := .call "\x009"
  [.builtin .mload [.var "\x00116"],
    .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 32)]],
    .builtin .mload [.lit (.number 1664)],
    .builtin .mload [.lit (.number 1696)]]

private theorem fp2InvStmt10_shape : fp2InvStmt10 =
    .assign ["\x00117", "\x00118"] fp2InvRealCall := by rfl

private theorem eval_fp2InvRealCall (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvScalarEnv yst out a) (fp2InvAfterScalarStores yst a)
      fp2InvRealCall =
    .ok (.vals [(fp2InvReal yst a).1, (fp2InvReal yst a).2]
      (fp2InvAfterRealCall yst a)) := by
  let s := fp2InvAfterScalarStores yst a
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
      (fp2InvScalarEnv yst out a) s
      [.builtin .mload [.var "\x00116"],
        .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 32)]],
        .builtin .mload [.lit (.number 1664)],
        .builtin .mload [.lit (.number 1696)]] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
      [("ahi", loadWord s.memory a.toNat),
        ("alo", loadWord s.memory (a + BitVec.ofNat 256 32).toNat),
        ("bhi", loadWord s.memory 1664), ("blo", loadWord s.memory 1696)]
      (fp2InvAfterRealReads yst a)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterRealReads,
      fp2AddReadState, fp2InvScalarEnv, fp2InvInitialEnv, s,
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

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
