import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvSquare0

set_option warningAsError true

/-! Second square in frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev fp2InvAfterSquare1Reads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare1Reads
abbrev fp2InvSquare1 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvSquare1
abbrev fp2InvAfterSquare1Call :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare1Call
abbrev fp2InvAfterSquare1High :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare1High
abbrev fp2InvAfterSquare1Stores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare1Stores

def fp2InvSquare1Env (yst : EvmState) (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00123", (fp2InvSquare1 yst a).1),
    ("\x00124", (fp2InvSquare1 yst a).2)] ++ fp2InvInitialEnv out a

private def fp2InvCall3 : Expr Op := .call "\x009"
  [.builtin .mload [.builtin .add [.var "\x00122", .lit (.number 64)]],
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 96)]],
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 64)]],
    .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 96)]]]

private theorem fp2InvStmt3_shape : fp2InvStmt3 =
    .assign ["\x00123", "\x00124"] fp2InvCall3 := by rfl

private theorem eval_fp2InvCall3 (yst : EvmState) (out a : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2InvBodyFuns
      (fp2InvSquare0Env yst out a) (fp2InvAfterSquare0Stores yst a)
      fp2InvCall3 =
    .ok (.vals [(fp2InvSquare1 yst a).1, (fp2InvSquare1 yst a).2]
      (fp2InvAfterSquare1Call yst a)) := by
  let s := fp2InvAfterSquare0Stores yst a
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2InvBodyFuns
          (fp2InvSquare0Env yst out a) s
          [.builtin .mload [.builtin .add [.var "\x00122", .lit (.number 64)]],
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 96)]],
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 64)]],
            .builtin .mload [.builtin .add [.var "\x00122", .lit (.number 96)]]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
          [("ahi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("alo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat),
            ("bhi", loadWord s.memory (a + BitVec.ofNat 256 64).toNat),
            ("blo", loadWord s.memory (a + BitVec.ofNat 256 96).toNat)]
          (fp2InvAfterSquare1Reads yst a)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2InvAfterSquare1Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterSquare1Reads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState,
      fp2InvSquare0Env, fp2InvInitialEnv, s,
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
    .ok (fp2InvSquare1Env yst out a, fp2InvAfterSquare1Call yst a,
      .normal) := by
  rw [fp2InvStmt3_shape, Interp.execStmt, eval_fp2InvCall3]
  rfl

theorem exec_fp2InvSquare1Stores (yst : EvmState) (out a : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2InvBodyFuns
      (fp2InvSquare1Env yst out a) (fp2InvAfterSquare1Call yst a)
      [fp2InvStmt4, fp2InvStmt5] =
    .ok (fp2InvSquare1Env yst out a, fp2InvAfterSquare1Stores yst a,
      .normal) := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
