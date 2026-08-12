import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulReal

set_option warningAsError true

/-! # Left component sum in frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl
private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def fp2MulAfterSumAReads (yst : EvmState) (out a b : U256) : EvmState :=
  fp2AddReadState (fp2MulAfterRealStores yst out a b)
    a (a + BitVec.ofNat 256 32)
    (a + BitVec.ofNat 256 64) (a + BitVec.ofNat 256 96)

def fp2MulSumA (yst : EvmState) (out a b : U256) : U256 × U256 :=
  let s := fp2MulAfterRealStores yst out a b
  fpAddValue (loadWord s.memory a.toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)

def fp2MulSumAEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00113", (fp2MulSumA yst out a b).1), ("\x00114", (fp2MulSumA yst out a b).2)] ++
    fp2MulInitialEnv out a b

def fp2MulAfterSumAHigh (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2MulAfterSumAReads yst out a b) 1664
    (fp2MulSumA yst out a b).1
def fp2MulAfterSumAStores (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2MulAfterSumAHigh yst out a b) 1696
    (fp2MulSumA yst out a b).2

private def fp2MulSumACall : Expr Op :=
  .call "\x004"
    [.builtin .mload [.var "\x00111"],
      .builtin .mload [.builtin .add [.var "\x00111", .lit (.number 32)]],
      .builtin .mload [.builtin .add [.var "\x00111", .lit (.number 64)]],
      .builtin .mload [.builtin .add [.var "\x00111", .lit (.number 96)]]]
private theorem fp2MulStmt9_shape : fp2MulStmt9 =
    .assign ["\x00113", "\x00114"] fp2MulSumACall := by rfl

private theorem eval_fp2MulSumACall (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2MulBodyFuns
      (fp2MulRealEnv yst out a b) (fp2MulAfterRealStores yst out a b)
      fp2MulSumACall =
    .ok (.vals [(fp2MulSumA yst out a b).1, (fp2MulSumA yst out a b).2]
      (fp2MulAfterSumAReads yst out a b)) := by
  let s := fp2MulAfterRealStores yst out a b
  have hget : VEnv.get (fp2MulRealEnv yst out a b) "\x00111" = some a := by
    rfl
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2MulBodyFuns
          (fp2MulRealEnv yst out a b) s
          [.builtin .mload [.var "\x00111"],
            .builtin .mload [.builtin .add [.var "\x00111", .lit (.number 32)]],
            .builtin .mload [.builtin .add [.var "\x00111", .lit (.number 64)]],
            .builtin .mload [.builtin .add [.var "\x00111", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
          [("ahi", loadWord s.memory a.toNat),
            ("alo", loadWord s.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat)]
          (fp2MulAfterSumAReads yst out a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterSumAReads,
      fp2AddReadState, hget, s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, EVM.litValue]
    rfl
  have hlookup : lookupFun fp2MulBodyFuns "\x004" = lookupFun fp2Funs "\x004" := by rfl
  rw [fp2MulSumACall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup]
  rw [show fp2Funs = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpAdd]
  rfl

theorem exec_fp2MulStmt9 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2MulBodyFuns
      (fp2MulRealEnv yst out a b) (fp2MulAfterRealStores yst out a b)
      fp2MulStmt9 =
    .ok (fp2MulSumAEnv yst out a b, fp2MulAfterSumAReads yst out a b, .normal) := by
  rw [fp2MulStmt9_shape, Interp.execStmt, eval_fp2MulSumACall]
  rfl

theorem exec_fp2MulSumAStores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulSumAEnv yst out a b) (fp2MulAfterSumAReads yst out a b)
      [fp2MulStmt10, fp2MulStmt11] =
    .ok (fp2MulSumAEnv yst out a b, fp2MulAfterSumAStores yst out a b, .normal) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
