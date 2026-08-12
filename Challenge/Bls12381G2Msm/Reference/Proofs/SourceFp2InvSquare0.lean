import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvDefs

set_option warningAsError true

/-! First square in frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2InvAfterSquare0Reads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare0Reads
abbrev fp2InvSquare0 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvSquare0
abbrev fp2InvAfterSquare0Call :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare0Call
abbrev fp2InvAfterSquare0High :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare0High
abbrev fp2InvAfterSquare0Stores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare0Stores

def fp2InvSquare0Env (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00123", (fp2InvSquare0 yst a).1),
    ("\x00124", (fp2InvSquare0 yst a).2)] ++ fp2InvInitialEnv out a

private def fp2InvCall0 : Expr Op := .call "\x009"
  [.builtin .mload [.var "\x00122"],
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 32)]],
    .builtin .mload [.var "\x00122"],
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 32)]]]

private theorem fp2InvStmt0_shape : fp2InvStmt0 =
    .letDecl ["\x00123", "\x00124"] (some fp2InvCall0) := by rfl

private theorem eval_fp2InvCall0 (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvInitialEnv out a) yst fp2InvCall0 =
    .ok (.vals [(fp2InvSquare0 yst a).1, (fp2InvSquare0 yst a).2]
      (fp2InvAfterSquare0Call yst a)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
          (fp2InvInitialEnv out a) yst
          [.builtin .mload [.var "\x00122"],
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 32)]],
            .builtin .mload [.var "\x00122"],
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 32)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", loadWord yst.memory a.toNat),
            ("alo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat),
            ("bhi", loadWord yst.memory a.toNat),
            ("blo", loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)]
          (fp2InvAfterSquare0Reads yst a)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterSquare0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare0Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      fp2InvInitialEnv, Challenge.EvmProof.modexpExec,
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
    .ok (fp2InvSquare0Env yst out a, fp2InvAfterSquare0Call yst a,
      .normal) := by
  rw [fp2InvStmt0_shape, Interp.execStmt, eval_fp2InvCall0]
  rfl

theorem exec_fp2InvSquare0Stores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvSquare0Env yst out a) (fp2InvAfterSquare0Call yst a)
      [fp2InvStmt1, fp2InvStmt2] =
    .ok (fp2InvSquare0Env yst out a, fp2InvAfterSquare0Stores yst a,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
