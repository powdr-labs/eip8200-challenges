import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubStart

set_option warningAsError true

/-! # Second component and body of frozen G2ADD `fp2Sub` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

def fp2SubC1Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fp2SubC0Env yst out a b) ["\x00108", "\x00109"]
    [(fp2SubC1 yst out a b).1, (fp2SubC1 yst out a b).2]

private def fp2SubCall1 : Expr Op :=
  .call "\x005"
    [.builtin .mload
        [.builtin .add [.var "\x00106", .lit (.number 64)]],
      .builtin .mload
        [.builtin .add [.var "\x00106", .lit (.number 96)]],
      .builtin .mload
        [.builtin .add [.var "\x00107", .lit (.number 64)]],
      .builtin .mload
        [.builtin .add [.var "\x00107", .lit (.number 96)]]]

private theorem fp2SubStmt3_shape : fp2SubStmt3 =
    .assign ["\x00108", "\x00109"] fp2SubCall1 := by
  rfl

private theorem eval_fpSub65 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 fp2SubFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpSubValue ahi alo bhi blo).1,
      (fpSubValue ahi alo bhi blo).2] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookupFun, hoist, fp2SubFuns, fp2Funs,
    Compilation.referenceCompiledBlock, Compilation.frozenReferenceBlock,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    stepOp, bin, Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set,
    bindZeros, restore]
  split
  case isTrue hsource =>
    have hnamed := hsource
    change fpSubNeedsRepairValue (fpSubRawValue ahi alo bhi blo) = 0 at hnamed
    unfold fpSubValue
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
    rw [if_pos hnamed]
    rfl
  case isFalse hsource =>
    have hnamed := hsource
    change ¬fpSubNeedsRepairValue (fpSubRawValue ahi alo bhi blo) = 0 at hnamed
    unfold fpSubValue
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
    rw [if_neg hnamed]
    rfl

private theorem eval_fp2SubCall1 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 fp2SubBodyFuns
      (fp2SubC0Env yst out a b) (fp2SubAfterC0Stores yst out a b)
      fp2SubCall1 =
    .ok (.vals [(fp2SubC1 yst out a b).1, (fp2SubC1 yst out a b).2]
      (fp2SubAfterC1Reads yst out a b)) := by
  let s := fp2SubAfterC0Stores yst out a b
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 64 fp2SubBodyFuns
          (fp2SubC0Env yst out a b) s
          [.builtin .mload
              [.builtin .add [.var "\x00106", .lit (.number 64)]],
            .builtin .mload
              [.builtin .add [.var "\x00106", .lit (.number 96)]],
            .builtin .mload
              [.builtin .add [.var "\x00107", .lit (.number 64)]],
            .builtin .mload
              [.builtin .add [.var "\x00107", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 64 fp2SubFuns
          [("ahi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("alo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat),
            ("bhi", loadWord s.memory (b + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (b + BitVec.ofNat 256 96).toNat)]
          (fp2SubAfterC1Reads yst out a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2SubAfterC1Reads,
      fp2SubReadState, fp2SubC0Env, fp2SubInitialEnv, s,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2SubBodyFuns "\x005" =
      lookupFun fp2SubFuns "\x005" := by
    rfl
  rw [fp2SubCall1, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x005") hargs hlookup]
  rw [eval_fpSub65]
  rfl

theorem exec_fp2SubStmt3 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 fp2SubBodyFuns
      (fp2SubC0Env yst out a b) (fp2SubAfterC0Stores yst out a b)
      fp2SubStmt3 =
    .ok (fp2SubC1Env yst out a b, fp2SubAfterC1Reads yst out a b,
      .normal) := by
  rw [fp2SubStmt3_shape, Interp.execStmt, eval_fp2SubCall1]
  rfl

theorem exec_fp2SubC1Stores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 66 fp2SubBodyFuns
      (fp2SubC1Env yst out a b) (fp2SubAfterC1Reads yst out a b)
      [fp2SubStmt4, fp2SubStmt5] =
    .ok (fp2SubC1Env yst out a b, fp2SubFinalState yst out a b,
      .normal) := by
  rfl

def fp2SubBodyResultEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fp2SubInitialEnv out a b) (fp2SubC1Env yst out a b)

theorem exec_fp2SubBody (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 71 fp2SubFuns
      (fp2SubInitialEnv out a b) yst (.block fp2SubBody) =
    .ok (fp2SubBodyResultEnv yst out a b, fp2SubFinalState yst out a b,
      .normal) := by
  have hsecond :
      Interp.execStmts Challenge.EvmProof.modexpExec 67 fp2SubBodyFuns
          (fp2SubC0Env yst out a b) (fp2SubAfterC0Stores yst out a b)
          [fp2SubStmt3, fp2SubStmt4, fp2SubStmt5] =
        .ok (fp2SubC1Env yst out a b, fp2SubFinalState yst out a b,
          .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fp2SubStmt3 yst out a b) (exec_fp2SubC1Stores yst out a b)
  have hfirstTail :
      Interp.execStmts Challenge.EvmProof.modexpExec 69 fp2SubBodyFuns
          (fp2SubC0Env yst out a b) (fp2SubAfterC0Reads yst a b)
          [fp2SubStmt1, fp2SubStmt2, fp2SubStmt3,
            fp2SubStmt4, fp2SubStmt5] =
        .ok (fp2SubC1Env yst out a b, fp2SubFinalState yst out a b,
          .normal) := by
    exact Interp.execStmts_append_normal (E := Challenge.EvmProof.modexpExec)
      (n := 67) (pre := [fp2SubStmt1, fp2SubStmt2])
      (tail := [fp2SubStmt3, fp2SubStmt4, fp2SubStmt5])
      (by omega) (exec_fp2SubC0Stores yst out a b) hsecond
  have hbody :
      Interp.execStmts Challenge.EvmProof.modexpExec 70 fp2SubBodyFuns
          (fp2SubInitialEnv out a b) yst
          [fp2SubStmt0, fp2SubStmt1, fp2SubStmt2,
            fp2SubStmt3, fp2SubStmt4, fp2SubStmt5] =
        .ok (fp2SubC1Env yst out a b, fp2SubFinalState yst out a b,
          .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fp2SubStmt0 yst out a b) hfirstTail
  rw [Interp.execStmt, fp2SubBodyFuns_eq, fp2SubBody_eq, hbody]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
