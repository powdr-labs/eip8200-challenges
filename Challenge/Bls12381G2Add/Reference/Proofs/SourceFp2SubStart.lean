import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # First component of frozen G2ADD `fp2Sub` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

def fp2SubC0Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00108", (fp2SubC0 yst a b).1),
    ("\x00109", (fp2SubC0 yst a b).2)] ++ fp2SubInitialEnv out a b

private def fp2SubCall0 : Expr Op :=
  .call "\x005"
    [.builtin .mload [.var "\x00106"],
      .builtin .mload
        [.builtin .add [.var "\x00106", .lit (.number 32)]],
      .builtin .mload [.var "\x00107"],
      .builtin .mload
        [.builtin .add [.var "\x00107", .lit (.number 32)]]]

private theorem fp2SubStmt0_shape : fp2SubStmt0 =
    .letDecl ["\x00108", "\x00109"] (some fp2SubCall0) := by
  rfl

private theorem eval_fpSub68 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2SubFuns
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

private theorem eval_fp2SubCall0 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2SubBodyFuns
      (fp2SubInitialEnv out a b) yst fp2SubCall0 =
    .ok (.vals [(fp2SubC0 yst a b).1, (fp2SubC0 yst a b).2]
      (fp2SubAfterC0Reads yst a b)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2SubBodyFuns
          (fp2SubInitialEnv out a b) yst
          [.builtin .mload [.var "\x00106"],
            .builtin .mload
              [.builtin .add [.var "\x00106", .lit (.number 32)]],
            .builtin .mload [.var "\x00107"],
            .builtin .mload
              [.builtin .add [.var "\x00107", .lit (.number 32)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2SubFuns
          [("ahi", loadWord yst.memory a.toNat),
            ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord yst.memory b.toNat),
            ("blo", loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)]
          (fp2SubAfterC0Reads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2SubAfterC0Reads,
      fp2SubReadState, fp2SubInitialEnv,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2SubBodyFuns "\x005" =
      lookupFun fp2SubFuns "\x005" := by
    rfl
  rw [fp2SubCall0, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x005") hargs hlookup]
  rw [eval_fpSub68]
  rfl

theorem exec_fp2SubStmt0 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2SubBodyFuns
      (fp2SubInitialEnv out a b) yst fp2SubStmt0 =
    .ok (fp2SubC0Env yst out a b, fp2SubAfterC0Reads yst a b,
      .normal) := by
  rw [fp2SubStmt0_shape, Interp.execStmt, eval_fp2SubCall0]
  rfl

theorem exec_fp2SubC0Stores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 69 fp2SubBodyFuns
      (fp2SubC0Env yst out a b) (fp2SubAfterC0Reads yst a b)
      [fp2SubStmt1, fp2SubStmt2] =
    .ok (fp2SubC0Env yst out a b, fp2SubAfterC0Stores yst out a b,
      .normal) := by
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
