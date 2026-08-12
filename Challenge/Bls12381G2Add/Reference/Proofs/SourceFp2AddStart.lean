import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # First component of frozen G2ADD `fp2Add` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

def fp2AddC0Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00103", (fp2AddC0 yst a b).1),
    ("\x00104", (fp2AddC0 yst a b).2)] ++ fp2AddInitialEnv out a b

private def fp2AddCall0 : Expr Op :=
  .call "\x004"
    [.builtin .mload [.var "\x00101"],
      .builtin .mload
        [.builtin .add [.var "\x00101", .lit (.number 32)]],
      .builtin .mload [.var "\x00102"],
      .builtin .mload
        [.builtin .add [.var "\x00102", .lit (.number 32)]]]

private theorem fp2AddStmt0_shape : fp2AddStmt0 =
    .letDecl ["\x00103", "\x00104"] (some fp2AddCall0) := by
  rfl

private theorem eval_fpAdd68 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2AddFuns
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

private theorem eval_fp2AddCall0 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2AddBodyFuns
      (fp2AddInitialEnv out a b) yst fp2AddCall0 =
    .ok (.vals [(fp2AddC0 yst a b).1, (fp2AddC0 yst a b).2]
      (fp2AddAfterC0Reads yst a b)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2AddBodyFuns
          (fp2AddInitialEnv out a b) yst
          [.builtin .mload [.var "\x00101"],
            .builtin .mload
              [.builtin .add [.var "\x00101", .lit (.number 32)]],
            .builtin .mload [.var "\x00102"],
            .builtin .mload
              [.builtin .add [.var "\x00102", .lit (.number 32)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2AddFuns
          [("ahi", loadWord yst.memory a.toNat),
            ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord yst.memory b.toNat),
            ("blo", loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)]
          (fp2AddAfterC0Reads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2AddAfterC0Reads,
      fp2AddReadState, fp2AddInitialEnv,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2AddBodyFuns "\x004" =
      lookupFun fp2AddFuns "\x004" := by
    rfl
  rw [fp2AddCall0, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup]
  rw [eval_fpAdd68]
  rfl

theorem exec_fp2AddStmt0 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 fp2AddBodyFuns
      (fp2AddInitialEnv out a b) yst fp2AddStmt0 =
    .ok (fp2AddC0Env yst out a b, fp2AddAfterC0Reads yst a b,
      .normal) := by
  rw [fp2AddStmt0_shape, Interp.execStmt, eval_fp2AddCall0]
  rfl

theorem exec_fp2AddC0Stores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 69 fp2AddBodyFuns
      (fp2AddC0Env yst out a b) (fp2AddAfterC0Reads yst a b)
      [fp2AddStmt1, fp2AddStmt2] =
    .ok (fp2AddC0Env yst out a b, fp2AddAfterC0Stores yst out a b,
      .normal) := by
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
