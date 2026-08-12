import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvDefs

set_option warningAsError true
/-! # First square in frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def fp2InvAfterSquare0Reads (yst : EvmState) (a : U256) : EvmState :=
  fp2AddReadState yst a (a + BitVec.ofNat 256 32)
    a (a + BitVec.ofNat 256 32)

def fp2InvSquare0 (yst : EvmState) (a : U256) : U256 × U256 :=
  fpMulResult (fp2InvAfterSquare0Reads yst a)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)

def fp2InvAfterSquare0Call (yst : EvmState) (a : U256) : EvmState :=
  fpMulFinalState (fp2InvAfterSquare0Reads yst a)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)

def fp2InvSquare0Env (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00117", (fp2InvSquare0 yst a).1),
    ("\x00118", (fp2InvSquare0 yst a).2)] ++ fp2InvInitialEnv out a

def fp2InvAfterSquare0High (yst : EvmState) (a : U256) : EvmState :=
  mstoreState (fp2InvAfterSquare0Call yst a) 1536 (fp2InvSquare0 yst a).1
def fp2InvAfterSquare0Stores (yst : EvmState) (a : U256) : EvmState :=
  mstoreState (fp2InvAfterSquare0High yst a) 1568 (fp2InvSquare0 yst a).2

private def fp2InvCall0 : Expr Op := .call "\x009"
  [.builtin .mload [.var "\x00116"],
    .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 32)]],
    .builtin .mload [.var "\x00116"],
    .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 32)]]]

private theorem fp2InvStmt0_shape : fp2InvStmt0 =
    .letDecl ["\x00117", "\x00118"] (some fp2InvCall0) := by rfl

private theorem eval_fp2InvCall0 (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvInitialEnv out a) yst fp2InvCall0 =
    .ok (.vals [(fp2InvSquare0 yst a).1, (fp2InvSquare0 yst a).2]
      (fp2InvAfterSquare0Call yst a)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
      (fp2InvInitialEnv out a) yst
      [.builtin .mload [.var "\x00116"],
        .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 32)]],
        .builtin .mload [.var "\x00116"],
        .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 32)]]] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
      [("ahi", loadWord yst.memory a.toNat),
        ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
        ("bhi", loadWord yst.memory a.toNat),
        ("blo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)]
      (fp2InvAfterSquare0Reads yst a)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterSquare0Reads,
      fp2AddReadState, fp2InvInitialEnv, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2InvBodyFuns "\x009" =
      lookupFun fpMulFuns "\x009" := by rfl
  rw [fp2InvCall0, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup]
  rw [show fpMulFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpMul]
  rfl

theorem exec_fp2InvStmt0 (yst : EvmState) (out a : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2InvBodyFuns
      (fp2InvInitialEnv out a) yst fp2InvStmt0 =
    .ok (fp2InvSquare0Env yst out a, fp2InvAfterSquare0Call yst a, .normal) := by
  rw [fp2InvStmt0_shape, Interp.execStmt, eval_fp2InvCall0]
  rfl

theorem exec_fp2InvSquare0Stores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvSquare0Env yst out a) (fp2InvAfterSquare0Call yst a)
      [fp2InvStmt1, fp2InvStmt2] =
    .ok (fp2InvSquare0Env yst out a, fp2InvAfterSquare0Stores yst a,
      .normal) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
