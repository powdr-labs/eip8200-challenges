import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2MulDefs
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

/-! First scalar product in frozen G2MSM `fp2Mul`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2MulAfterV0Reads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterV0Reads
abbrev fp2MulV0 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulV0
abbrev fp2MulAfterV0Call :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterV0Call
abbrev fp2MulAfterV0High :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterV0High
abbrev fp2MulAfterV0Stores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterV0Stores

def fp2MulV0Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00119", (fp2MulV0 yst a b).1),
    ("\x00120", (fp2MulV0 yst a b).2)] ++ fp2MulInitialEnv out a b

private def fp2MulCall0 : Expr Op :=
  .call "\x009"
    [.builtin .mload [.var "\x00117"],
      .builtin .mload
        [.builtin .add [.var "\x00117", .lit (.number 32)]],
      .builtin .mload [.var "\x00118"],
      .builtin .mload
        [.builtin .add [.var "\x00118", .lit (.number 32)]]]

private theorem fp2MulStmt0_shape : fp2MulStmt0 =
    .letDecl ["\x00119", "\x00120"] (some fp2MulCall0) := by
  rfl

private theorem eval_fp2MulCall0 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2MulBodyFuns
      (fp2MulInitialEnv out a b) yst fp2MulCall0 =
    .ok (.vals [(fp2MulV0 yst a b).1, (fp2MulV0 yst a b).2]
      (fp2MulAfterV0Call yst a b)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2MulBodyFuns
          (fp2MulInitialEnv out a b) yst
          [.builtin .mload [.var "\x00117"],
            .builtin .mload
              [.builtin .add [.var "\x00117", .lit (.number 32)]],
            .builtin .mload [.var "\x00118"],
            .builtin .mload
              [.builtin .add [.var "\x00118", .lit (.number 32)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", loadWord yst.memory a.toNat),
            ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord yst.memory b.toNat),
            ("blo", loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)]
          (fp2MulAfterV0Reads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterV0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterV0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      fp2MulInitialEnv,
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

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
