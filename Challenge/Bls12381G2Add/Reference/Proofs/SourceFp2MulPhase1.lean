import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulPhase0

set_option warningAsError true

/-! # Second scalar product in frozen G2ADD `fp2Mul` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) :
    EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def fp2MulAfterV1Reads (yst : EvmState) (a b : U256) : EvmState :=
  fp2AddReadState (fp2MulAfterV0Stores yst a b)
    (a + BitVec.ofNat 256 64) (a + BitVec.ofNat 256 96)
    (b + BitVec.ofNat 256 64) (b + BitVec.ofNat 256 96)

def fp2MulV1 (yst : EvmState) (a b : U256) : U256 × U256 :=
  let s := fp2MulAfterV0Stores yst a b
  fpMulResult (fp2MulAfterV1Reads yst a b)
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 96).toNat)

def fp2MulAfterV1Call (yst : EvmState) (a b : U256) : EvmState :=
  let s := fp2MulAfterV0Stores yst a b
  fpMulFinalState (fp2MulAfterV1Reads yst a b)
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 96).toNat)

def fp2MulV1Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00113", (fp2MulV1 yst a b).1), ("\x00114", (fp2MulV1 yst a b).2)] ++
    fp2MulInitialEnv out a b

def fp2MulAfterV1High (yst : EvmState) (a b : U256) : EvmState :=
  mstoreState (fp2MulAfterV1Call yst a b) 1600 (fp2MulV1 yst a b).1

def fp2MulAfterV1Stores (yst : EvmState) (a b : U256) : EvmState :=
  mstoreState (fp2MulAfterV1High yst a b) 1632 (fp2MulV1 yst a b).2

private def fp2MulCall1 : Expr Op :=
  .call "\x009"
    [.builtin .mload
        [.builtin .add [.var "\x00111", .lit (.number 64)]],
      .builtin .mload
        [.builtin .add [.var "\x00111", .lit (.number 96)]],
      .builtin .mload
        [.builtin .add [.var "\x00112", .lit (.number 64)]],
      .builtin .mload
        [.builtin .add [.var "\x00112", .lit (.number 96)]]]

private theorem fp2MulStmt3_shape : fp2MulStmt3 =
    .assign ["\x00113", "\x00114"] fp2MulCall1 := by rfl

private theorem eval_fp2MulCall1 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2MulBodyFuns
      (fp2MulV0Env yst out a b) (fp2MulAfterV0Stores yst a b)
      fp2MulCall1 =
    .ok (.vals [(fp2MulV1 yst a b).1, (fp2MulV1 yst a b).2]
      (fp2MulAfterV1Call yst a b)) := by
  let s := fp2MulAfterV0Stores yst a b
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2MulBodyFuns
          (fp2MulV0Env yst out a b) s
          [.builtin .mload
              [.builtin .add [.var "\x00111", .lit (.number 64)]],
            .builtin .mload
              [.builtin .add [.var "\x00111", .lit (.number 96)]],
            .builtin .mload
              [.builtin .add [.var "\x00112", .lit (.number 64)]],
            .builtin .mload
              [.builtin .add [.var "\x00112", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("alo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat),
            ("bhi", loadWord s.memory (b + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (b + BitVec.ofNat 256 96).toNat)]
          (fp2MulAfterV1Reads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterV1Reads,
      fp2AddReadState, fp2MulV0Env, fp2MulInitialEnv, s,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2MulBodyFuns "\x009" =
      lookupFun fpMulFuns "\x009" := by rfl
  rw [fp2MulCall1, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup]
  rw [show fpMulFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul]
  rfl

theorem exec_fp2MulStmt3 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2MulBodyFuns
      (fp2MulV0Env yst out a b) (fp2MulAfterV0Stores yst a b)
      fp2MulStmt3 =
    .ok (fp2MulV1Env yst out a b, fp2MulAfterV1Call yst a b,
      .normal) := by
  rw [fp2MulStmt3_shape, Interp.execStmt, eval_fp2MulCall1]
  rfl

theorem exec_fp2MulV1Stores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulV1Env yst out a b) (fp2MulAfterV1Call yst a b)
      [fp2MulStmt4, fp2MulStmt5] =
    .ok (fp2MulV1Env yst out a b, fp2MulAfterV1Stores yst a b,
      .normal) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
