import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainValidationLawful

set_option warningAsError true

/-! # Frozen G1ADD point-validation prefix execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def zeroCall (hiOffset loOffset : Nat) : Expr Op :=
  .call "\x002"
    [.builtin .mload [.lit (.number hiOffset)],
      .builtin .mload [.lit (.number loOffset)]]

private def zeroPair (hi0 lo0 hi1 lo1 : Nat) : Expr Op :=
  .builtin .and [zeroCall hi0 lo0, zeroCall hi1 lo1]

private def afterTwoZeroLoads (yst : EvmState) (hiOffset loOffset : Nat) :
    EvmState := touchMemory (touchMemory yst loOffset 32) hiOffset 32

@[simp] private theorem touchMemory_memory (yst : EvmState) (offset size : Nat) :
    (touchMemory yst offset size).memory = yst.memory := rfl

private theorem eval_fpZero63 (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 63 mainFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x002" [.var "hi", .var "lo"]) =
    .ok (.vals [fpZeroValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

private theorem eval_fpZero_mload63
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (hiOffset loOffset : Nat)
    (hhi : hiOffset < 2 ^ 256) (hlo : loOffset < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 63 mainFuns V yst
      (zeroCall hiOffset loOffset) =
      .ok (.vals
        [fpZeroValue (loadWord yst.memory hiOffset)
          (loadWord yst.memory loOffset)]
        (afterTwoZeroLoads yst hiOffset loOffset)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 62 mainFuns V yst
          [.builtin .mload [.lit (.number hiOffset)],
            .builtin .mload [.lit (.number loOffset)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 62 mainFuns
          [("hi", loadWord yst.memory hiOffset),
            ("lo", loadWord yst.memory loOffset)]
          (afterTwoZeroLoads yst hiOffset loOffset)
          [.var "hi", .var "lo"] := by
    norm_num at hhi hlo
    simp [Interp.evalArgs, Interp.evalExpr, afterTwoZeroLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt hhi,
      Nat.mod_eq_of_lt hlo, VEnv.get]
  have hlookup : lookupFun mainFuns "\x002" = lookupFun mainFuns "\x002" := rfl
  rw [zeroCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x002") hargs hlookup]
  exact eval_fpZero63 _ _ _

private theorem eval_fpZero_mload64
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (hiOffset loOffset : Nat)
    (hhi : hiOffset < 2 ^ 256) (hlo : loOffset < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 mainFuns V yst
      (zeroCall hiOffset loOffset) =
      .ok (.vals
        [fpZeroValue (loadWord yst.memory hiOffset)
          (loadWord yst.memory loOffset)]
        (afterTwoZeroLoads yst hiOffset loOffset)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 mainFuns V yst
          [.builtin .mload [.lit (.number hiOffset)],
            .builtin .mload [.lit (.number loOffset)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 mainFuns
          [("hi", loadWord yst.memory hiOffset),
            ("lo", loadWord yst.memory loOffset)]
          (afterTwoZeroLoads yst hiOffset loOffset)
          [.var "hi", .var "lo"] := by
    norm_num at hhi hlo
    simp [Interp.evalArgs, Interp.evalExpr, afterTwoZeroLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt hhi,
      Nat.mod_eq_of_lt hlo, VEnv.get]
  have hlookup : lookupFun mainFuns "\x002" =
      lookupFun [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock] "\x002" := by rfl
  rw [zeroCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x002") hargs hlookup]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpZero _ _ _

private theorem eval_zeroPair
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (hi0 lo0 hi1 lo1 : Nat)
    (hhi0 : hi0 < 2 ^ 256) (hlo0 : lo0 < 2 ^ 256)
    (hhi1 : hi1 < 2 ^ 256) (hlo1 : lo1 < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 66 mainFuns V yst
      (zeroPair hi0 lo0 hi1 lo1) =
      .ok (.vals
        [fpZeroValue (loadWord yst.memory hi0) (loadWord yst.memory lo0) &&&
          fpZeroValue (loadWord yst.memory hi1) (loadWord yst.memory lo1)]
        (afterTwoZeroLoads (afterTwoZeroLoads yst hi1 lo1) hi0 lo0)) := by
  rw [zeroPair, Interp.evalExpr, Interp.evalArgs,
    Interp.evalArgs, Interp.evalArgs]
  simp
  rw [eval_fpZero_mload63 V yst hi1 lo1 hhi1 hlo1]
  simp
  rw [eval_fpZero_mload64 V (afterTwoZeroLoads yst hi1 lo1)
    hi0 lo0 hhi0 hlo0]
  simp [Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin,
    afterTwoZeroLoads]

private theorem mainInf1Stmt_shape : mainInf1Stmt =
    .letDecl ["\x0096"] (some (zeroPair 0 32 64 96)) := by rfl

theorem exec_mainInf1 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 mainFuns []
      (mainAfterCanonicalReads yst) mainInf1Stmt =
      .ok ([("\x0096", mainInf1 yst)], mainAfterInf1Reads yst,
        .normal) := by
  rw [mainInf1Stmt_shape, Interp.execStmt,
    eval_zeroPair [] _ 0 32 64 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
  simp [mainInf1, mainAfterInf1Reads, mainDecodedWord,
    mainAfterCanonicalReads, mainAfterPaddingReads, afterTwoZeroLoads]

private theorem mainInf2Stmt_shape : mainInf2Stmt =
    .letDecl ["\x0097"] (some (zeroPair 128 160 192 224)) := by rfl

theorem exec_mainInf2 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 mainFuns
      [("\x0096", mainInf1 yst)] (mainAfterInf1Reads yst) mainInf2Stmt =
      .ok (mainPointEnv yst, mainAfterInf2Reads yst, .normal) := by
  rw [mainInf2Stmt_shape, Interp.execStmt,
    eval_zeroPair [("\x0096", mainInf1 yst)] _ 128 160 192 224
      (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
  simp [mainInf2, mainPointEnv, mainAfterInf2Reads, mainDecodedWord,
    mainAfterInf1Reads, mainAfterCanonicalReads, mainAfterPaddingReads,
    afterTwoZeroLoads]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
