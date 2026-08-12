import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvSquare0

set_option warningAsError true
/-! # Second square in frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def fp2InvAfterSquare1Reads (yst : EvmState) (a : U256) : EvmState :=
  fp2AddReadState (fp2InvAfterSquare0Stores yst a)
    (a + BitVec.ofNat 256 64) (a + BitVec.ofNat 256 96)
    (a + BitVec.ofNat 256 64) (a + BitVec.ofNat 256 96)

def fp2InvSquare1 (yst : EvmState) (a : U256) : U256 × U256 :=
  let s := fp2InvAfterSquare0Stores yst a
  fpMulResult (fp2InvAfterSquare1Reads yst a)
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)

def fp2InvAfterSquare1Call (yst : EvmState) (a : U256) : EvmState :=
  let s := fp2InvAfterSquare0Stores yst a
  fpMulFinalState (fp2InvAfterSquare1Reads yst a)
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)

def fp2InvSquare1Env (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00117", (fp2InvSquare1 yst a).1),
    ("\x00118", (fp2InvSquare1 yst a).2)] ++ fp2InvInitialEnv out a

def fp2InvAfterSquare1High (yst : EvmState) (a : U256) : EvmState :=
  mstoreState (fp2InvAfterSquare1Call yst a) 1600 (fp2InvSquare1 yst a).1
def fp2InvAfterSquare1Stores (yst : EvmState) (a : U256) : EvmState :=
  mstoreState (fp2InvAfterSquare1High yst a) 1632 (fp2InvSquare1 yst a).2

private def fp2InvCall3 : Expr Op := .call "\x009"
  [.builtin .mload [.builtin .add [.var "\x00116", .lit (.number 64)]],
    .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 96)]],
    .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 64)]],
    .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 96)]]]

private theorem fp2InvStmt3_shape : fp2InvStmt3 =
    .assign ["\x00117", "\x00118"] fp2InvCall3 := by rfl

private theorem eval_fp2InvCall3 (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvSquare0Env yst out a) (fp2InvAfterSquare0Stores yst a)
      fp2InvCall3 =
    .ok (.vals [(fp2InvSquare1 yst a).1, (fp2InvSquare1 yst a).2]
      (fp2InvAfterSquare1Call yst a)) := by
  let s := fp2InvAfterSquare0Stores yst a
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
      (fp2InvSquare0Env yst out a) s
      [.builtin .mload [.builtin .add [.var "\x00116", .lit (.number 64)]],
        .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 96)]],
        .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 64)]],
        .builtin .mload [.builtin .add [.var "\x00116", .lit (.number 96)]]] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
      [("ahi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
        ("alo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat),
        ("bhi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
        ("blo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat)]
      (fp2InvAfterSquare1Reads yst a)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterSquare1Reads,
      fp2AddReadState, fp2InvSquare0Env, fp2InvInitialEnv, s,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2InvBodyFuns "\x009" =
      lookupFun fpMulFuns "\x009" := by rfl
  rw [fp2InvCall3, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup]
  rw [show fpMulFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpMul]
  rfl

theorem exec_fp2InvStmt3 (yst : EvmState) (out a : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2InvBodyFuns
      (fp2InvSquare0Env yst out a) (fp2InvAfterSquare0Stores yst a)
      fp2InvStmt3 =
    .ok (fp2InvSquare1Env yst out a, fp2InvAfterSquare1Call yst a, .normal) := by
  rw [fp2InvStmt3_shape, Interp.execStmt, eval_fp2InvCall3]
  rfl

theorem exec_fp2InvSquare1Stores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvSquare1Env yst out a) (fp2InvAfterSquare1Call yst a)
      [fp2InvStmt4, fp2InvStmt5] =
    .ok (fp2InvSquare1Env yst out a, fp2InvAfterSquare1Stores yst a,
      .normal) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
