import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddStart

set_option warningAsError true

/-! # Second component and body of frozen G2ADD `fp2Add` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

def fp2AddC1Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fp2AddC0Env yst out a b) ["\x00103", "\x00104"]
    [(fp2AddC1 yst out a b).1, (fp2AddC1 yst out a b).2]

private def fp2AddCall1 : Expr Op :=
  .call "\x004"
    [.builtin .mload
        [.builtin .add [.var "\x00101", .lit (.number 64)]],
      .builtin .mload
        [.builtin .add [.var "\x00101", .lit (.number 96)]],
      .builtin .mload
        [.builtin .add [.var "\x00102", .lit (.number 64)]],
      .builtin .mload
        [.builtin .add [.var "\x00102", .lit (.number 96)]]]

private theorem fp2AddStmt3_shape : fp2AddStmt3 =
    .assign ["\x00103", "\x00104"] fp2AddCall1 := by
  rfl

private theorem eval_fpAdd65 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 fp2AddFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x004" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpAddValue ahi alo bhi blo).1,
      (fpAddValue ahi alo bhi blo).2] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookupFun, hoist, fp2AddFuns, fp2Funs,
    Compilation.referenceCompiledBlock, Compilation.frozenReferenceBlock,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    stepOp, bin, un, Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set,
    bindZeros, restore]
  split
  case isTrue hsource =>
    have hnamed := hsource
    change fpGeModulusValue
      (ahi + bhi + b2w (BitVec.ult (alo + blo) alo)) (alo + blo) = 0 at hnamed
    simp [fpAddValue,
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue,
      hnamed]
  case isFalse hsource =>
    have hnamed := hsource
    change ¬fpGeModulusValue
      (ahi + bhi + b2w (BitVec.ult (alo + blo) alo)) (alo + blo) = 0 at hnamed
    unfold fpAddValue
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue
    rw [if_neg hnamed]
    rfl

private theorem eval_fp2AddCall1 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 fp2AddBodyFuns
      (fp2AddC0Env yst out a b) (fp2AddAfterC0Stores yst out a b)
      fp2AddCall1 =
    .ok (.vals [(fp2AddC1 yst out a b).1, (fp2AddC1 yst out a b).2]
      (fp2AddAfterC1Reads yst out a b)) := by
  let s := fp2AddAfterC0Stores yst out a b
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 64 fp2AddBodyFuns
          (fp2AddC0Env yst out a b) s
          [.builtin .mload
              [.builtin .add [.var "\x00101", .lit (.number 64)]],
            .builtin .mload
              [.builtin .add [.var "\x00101", .lit (.number 96)]],
            .builtin .mload
              [.builtin .add [.var "\x00102", .lit (.number 64)]],
            .builtin .mload
              [.builtin .add [.var "\x00102", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 64 fp2AddFuns
          [("ahi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("alo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat),
            ("bhi", loadWord s.memory (b + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (b + BitVec.ofNat 256 96).toNat)]
          (fp2AddAfterC1Reads yst out a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2AddAfterC1Reads,
      fp2AddReadState, fp2AddC0Env, fp2AddInitialEnv, s,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2AddBodyFuns "\x004" =
      lookupFun fp2AddFuns "\x004" := by
    rfl
  rw [fp2AddCall1, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup]
  rw [eval_fpAdd65]
  rfl

theorem exec_fp2AddStmt3 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 fp2AddBodyFuns
      (fp2AddC0Env yst out a b) (fp2AddAfterC0Stores yst out a b)
      fp2AddStmt3 =
    .ok (fp2AddC1Env yst out a b, fp2AddAfterC1Reads yst out a b,
      .normal) := by
  rw [fp2AddStmt3_shape, Interp.execStmt, eval_fp2AddCall1]
  rfl

theorem exec_fp2AddC1Stores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 66 fp2AddBodyFuns
      (fp2AddC1Env yst out a b) (fp2AddAfterC1Reads yst out a b)
      [fp2AddStmt4, fp2AddStmt5] =
    .ok (fp2AddC1Env yst out a b, fp2AddFinalState yst out a b,
      .normal) := by
  rfl

def fp2AddBodyResultEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fp2AddInitialEnv out a b) (fp2AddC1Env yst out a b)

theorem exec_fp2AddBody (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 71 fp2AddFuns
      (fp2AddInitialEnv out a b) yst (.block fp2AddBody) =
    .ok (fp2AddBodyResultEnv yst out a b, fp2AddFinalState yst out a b,
      .normal) := by
  have hsecond :
      Interp.execStmts Challenge.EvmProof.modexpExec 67 fp2AddBodyFuns
          (fp2AddC0Env yst out a b) (fp2AddAfterC0Stores yst out a b)
          [fp2AddStmt3, fp2AddStmt4, fp2AddStmt5] =
        .ok (fp2AddC1Env yst out a b, fp2AddFinalState yst out a b,
          .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fp2AddStmt3 yst out a b) (exec_fp2AddC1Stores yst out a b)
  have hfirstTail :
      Interp.execStmts Challenge.EvmProof.modexpExec 69 fp2AddBodyFuns
          (fp2AddC0Env yst out a b) (fp2AddAfterC0Reads yst a b)
          [fp2AddStmt1, fp2AddStmt2, fp2AddStmt3,
            fp2AddStmt4, fp2AddStmt5] =
        .ok (fp2AddC1Env yst out a b, fp2AddFinalState yst out a b,
          .normal) := by
    exact Interp.execStmts_append_normal (E := Challenge.EvmProof.modexpExec)
      (n := 67) (pre := [fp2AddStmt1, fp2AddStmt2])
      (tail := [fp2AddStmt3, fp2AddStmt4, fp2AddStmt5])
      (by omega) (exec_fp2AddC0Stores yst out a b) hsecond
  have hbody :
      Interp.execStmts Challenge.EvmProof.modexpExec 70 fp2AddBodyFuns
          (fp2AddInitialEnv out a b) yst
          [fp2AddStmt0, fp2AddStmt1, fp2AddStmt2,
            fp2AddStmt3, fp2AddStmt4, fp2AddStmt5] =
        .ok (fp2AddC1Env yst out a b, fp2AddFinalState yst out a b,
          .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fp2AddStmt0 yst out a b) hfirstTail
  rw [Interp.execStmt, fp2AddBodyFuns_eq, fp2AddBody_eq, hbody]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
