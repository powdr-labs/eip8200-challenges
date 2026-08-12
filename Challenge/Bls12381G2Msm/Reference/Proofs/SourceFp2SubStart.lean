import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpSubFuel
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! First component of frozen G2MSM `fp2Sub`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fp2SubC0Env (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00114", (fp2SubC0 yst a b).1),
    ("\x00115", (fp2SubC0 yst a b).2)] ++ fp2SubInitialEnv out a b

private def fp2SubCall0 : Expr Op :=
  .call "\x005"
    [.builtin .mload [.var "\x00112"],
      .builtin .mload
        [.builtin .add [.var "\x00112", .lit (.number 32)]],
      .builtin .mload [.var "\x00113"],
      .builtin .mload
        [.builtin .add [.var "\x00113", .lit (.number 32)]]]

private theorem fp2SubStmt0_shape : fp2SubStmt0 =
    .letDecl ["\x00114", "\x00115"] (some fp2SubCall0) := by
  rfl

private theorem eval_fp2SubCall0 (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2SubBodyFuns
      (fp2SubInitialEnv out a b) yst fp2SubCall0 =
    .ok (.vals [(fp2SubC0 yst a b).1, (fp2SubC0 yst a b).2]
      (fp2SubAfterC0Reads yst a b)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2SubBodyFuns
          (fp2SubInitialEnv out a b) yst
          [.builtin .mload [.var "\x00112"],
            .builtin .mload
              [.builtin .add [.var "\x00112", .lit (.number 32)]],
            .builtin .mload [.var "\x00113"],
            .builtin .mload
              [.builtin .add [.var "\x00113", .lit (.number 32)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2SubFuns
          [("ahi", loadWord yst.memory a.toNat),
            ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord yst.memory b.toNat),
            ("blo", loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)]
          (fp2SubAfterC0Reads yst a b)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2SubAfterC0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubReadState,
      fp2SubInitialEnv,
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

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
