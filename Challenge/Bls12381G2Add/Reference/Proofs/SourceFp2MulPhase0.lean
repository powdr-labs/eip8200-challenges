import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulDefs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

/-! # First scalar product in frozen G2ADD `fp2Mul` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) :
    EvmState :=
  { touchMemory yst offset 32 with
    memory := storeWord yst.memory offset value }

def fp2MulAfterV0Reads (yst : EvmState) (a b : U256) : EvmState :=
  fp2AddReadState yst a (a + BitVec.ofNat 256 32)
    b (b + BitVec.ofNat 256 32)

def fp2MulV0 (yst : EvmState) (a b : U256) : U256 × U256 :=
  fpMulResult (fp2MulAfterV0Reads yst a b)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory b.toNat)
    (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)

def fp2MulAfterV0Call (yst : EvmState) (a b : U256) : EvmState :=
  fpMulFinalState (fp2MulAfterV0Reads yst a b)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory b.toNat)
    (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)

def fp2MulV0Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00113", (fp2MulV0 yst a b).1),
    ("\x00114", (fp2MulV0 yst a b).2)] ++ fp2MulInitialEnv out a b

def fp2MulAfterV0High (yst : EvmState) (a b : U256) : EvmState :=
  mstoreState (fp2MulAfterV0Call yst a b) 1536 (fp2MulV0 yst a b).1

def fp2MulAfterV0Stores (yst : EvmState) (a b : U256) : EvmState :=
  mstoreState (fp2MulAfterV0High yst a b) 1568 (fp2MulV0 yst a b).2

private def fp2MulCall0 : Expr Op :=
  .call "\x009"
    [.builtin .mload [.var "\x00111"],
      .builtin .mload
        [.builtin .add [.var "\x00111", .lit (.number 32)]],
      .builtin .mload [.var "\x00112"],
      .builtin .mload
        [.builtin .add [.var "\x00112", .lit (.number 32)]]]

private theorem fp2MulStmt0_shape : fp2MulStmt0 =
    .letDecl ["\x00113", "\x00114"] (some fp2MulCall0) := by
  rfl

private theorem eval_fp2MulCall0 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2MulBodyFuns
      (fp2MulInitialEnv out a b) yst fp2MulCall0 =
    .ok (.vals [(fp2MulV0 yst a b).1, (fp2MulV0 yst a b).2]
      (fp2MulAfterV0Call yst a b)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2MulBodyFuns
          (fp2MulInitialEnv out a b) yst
          [.builtin .mload [.var "\x00111"],
            .builtin .mload
              [.builtin .add [.var "\x00111", .lit (.number 32)]],
            .builtin .mload [.var "\x00112"],
            .builtin .mload
              [.builtin .add [.var "\x00112", .lit (.number 32)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", loadWord yst.memory a.toNat),
            ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord yst.memory b.toNat),
            ("blo", loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)]
          (fp2MulAfterV0Reads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterV0Reads,
      fp2AddReadState, fp2MulInitialEnv,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2MulBodyFuns "\x009" =
      lookupFun fpMulFuns "\x009" := by
    rfl
  rw [fp2MulCall0, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup]
  rw [show fpMulFuns =
    [hoist Challenge.EvmProof.modexpExec.toDialect
      Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul]
  rfl

theorem exec_fp2MulStmt0 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2MulBodyFuns
      (fp2MulInitialEnv out a b) yst fp2MulStmt0 =
    .ok (fp2MulV0Env yst out a b, fp2MulAfterV0Call yst a b,
      .normal) := by
  rw [fp2MulStmt0_shape, Interp.execStmt, eval_fp2MulCall0]
  rfl

theorem exec_fp2MulV0Stores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulV0Env yst out a b) (fp2MulAfterV0Call yst a b)
      [fp2MulStmt1, fp2MulStmt2] =
    .ok (fp2MulV0Env yst out a b, fp2MulAfterV0Stores yst a b,
      .normal) := by
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
