import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpAddFuel68
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! First component of frozen G2MSM `fp2Add`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fp2AddC0Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00109", (fp2AddC0 yst a b).1),
    ("\x00110", (fp2AddC0 yst a b).2)] ++ fp2AddInitialEnv out a b

private def fp2AddCall0 : Expr Op :=
  .call "\x004"
    [.builtin .mload [.var "\x00107"],
      .builtin .mload
        [.builtin .add [.var "\x00107", .lit (.number 32)]],
      .builtin .mload [.var "\x00108"],
      .builtin .mload
        [.builtin .add [.var "\x00108", .lit (.number 32)]]]

private theorem fp2AddStmt0_shape : fp2AddStmt0 =
    .letDecl ["\x00109", "\x00110"] (some fp2AddCall0) := by
  rfl

private theorem eval_fp2AddCall0 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2AddBodyFuns
      (fp2AddInitialEnv out a b) yst fp2AddCall0 =
    .ok (.vals [(fp2AddC0 yst a b).1, (fp2AddC0 yst a b).2]
      (fp2AddAfterC0Reads yst a b)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2AddBodyFuns
          (fp2AddInitialEnv out a b) yst
          [.builtin .mload [.var "\x00107"],
            .builtin .mload
              [.builtin .add [.var "\x00107", .lit (.number 32)]],
            .builtin .mload [.var "\x00108"],
            .builtin .mload
              [.builtin .add [.var "\x00108", .lit (.number 32)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2AddFuns
          [("ahi", loadWord yst.memory a.toNat),
            ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord yst.memory b.toNat),
            ("blo", loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)]
          (fp2AddAfterC0Reads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2AddAfterC0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      fp2AddInitialEnv,
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

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
