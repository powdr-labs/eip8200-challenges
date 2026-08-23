import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainDecodeExec

set_option warningAsError true

/-! # Frozen G1ADD main field-validation execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainInvalidState (yst : EvmState) : EvmState :=
  { yst with halted := some (.invalid, []) }

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

theorem exec_mainPadding (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 16 mainFuns []
      (mainDecodedState yst) mainPaddingStmt =
      if mainPaddingValue yst = 0 then
        .ok ([], mainAfterPaddingReads yst, .normal)
      else .ok ([], mainInvalidState (mainAfterPaddingReads yst), .halt) := by
  simp [mainPaddingStmt, Compilation.referenceCompiledBlock,
    Compilation.frozenReferenceBlock, mainPaddingValue, mainInvalidState,
    Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    mainAfterPaddingReads, mainDecodedWord, stepOp, bin, EVM.litValue,
    Dialect.zero, restore,
    touchMemory_memory]

theorem exec_mainPadding_success (yst : EvmState)
    (hpadding : mainPaddingValue yst = 0) :
    Interp.execStmt Challenge.EvmProof.modexpExec 16 mainFuns []
      (mainDecodedState yst) mainPaddingStmt =
      .ok ([], mainAfterPaddingReads yst, .normal) := by
  rw [exec_mainPadding, if_pos hpadding]

theorem exec_mainPadding_reject (yst : EvmState)
    (hpadding : mainPaddingValue yst ≠ 0) :
    Interp.execStmt Challenge.EvmProof.modexpExec 16 mainFuns []
      (mainDecodedState yst) mainPaddingStmt =
      .ok ([], mainInvalidState (mainAfterPaddingReads yst), .halt) := by
  rw [exec_mainPadding, if_neg hpadding]

private def afterTwoLoads (yst : EvmState) (hiOffset loOffset : Nat) :
    EvmState := touchMemory (touchMemory yst loOffset 32) hiOffset 32

private def validCall (hiOffset loOffset : Nat) : Expr Op :=
  .call "\x001"
    [.builtin .mload [.lit (.number hiOffset)],
      .builtin .mload [.lit (.number loOffset)]]

private theorem eval_fpValid62 (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 62 mainFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [fpValidValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

private theorem eval_fpValid63 (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 63 mainFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [fpValidValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

private theorem eval_fpValid_mload62 (yst : EvmState)
    (hiOffset loOffset : Nat)
    (hhi : hiOffset < 2 ^ 256) (hlo : loOffset < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 62 mainFuns [] yst
      (validCall hiOffset loOffset) =
      .ok (.vals
        [fpValidValue (loadWord yst.memory hiOffset)
          (loadWord yst.memory loOffset)]
        (afterTwoLoads yst hiOffset loOffset)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 61 mainFuns [] yst
          [.builtin .mload [.lit (.number hiOffset)],
            .builtin .mload [.lit (.number loOffset)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 61 mainFuns
          [("hi", loadWord yst.memory hiOffset),
            ("lo", loadWord yst.memory loOffset)]
          (afterTwoLoads yst hiOffset loOffset)
          [.var "hi", .var "lo"] := by
    norm_num at hhi hlo
    simp [Interp.evalArgs, Interp.evalExpr, afterTwoLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt hhi,
      Nat.mod_eq_of_lt hlo, VEnv.get]
  have hlookup : lookupFun mainFuns "\x001" = lookupFun mainFuns "\x001" := rfl
  rw [validCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x001") hargs hlookup]
  exact eval_fpValid62 _ _ _

private theorem eval_fpValid_mload63 (yst : EvmState)
    (hiOffset loOffset : Nat)
    (hhi : hiOffset < 2 ^ 256) (hlo : loOffset < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 63 mainFuns [] yst
      (validCall hiOffset loOffset) =
      .ok (.vals
        [fpValidValue (loadWord yst.memory hiOffset)
          (loadWord yst.memory loOffset)]
        (afterTwoLoads yst hiOffset loOffset)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 62 mainFuns [] yst
          [.builtin .mload [.lit (.number hiOffset)],
            .builtin .mload [.lit (.number loOffset)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 62 mainFuns
          [("hi", loadWord yst.memory hiOffset),
            ("lo", loadWord yst.memory loOffset)]
          (afterTwoLoads yst hiOffset loOffset)
          [.var "hi", .var "lo"] := by
    norm_num at hhi hlo
    simp [Interp.evalArgs, Interp.evalExpr, afterTwoLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt hhi,
      Nat.mod_eq_of_lt hlo, VEnv.get]
  have hlookup : lookupFun mainFuns "\x001" = lookupFun mainFuns "\x001" := rfl
  rw [validCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x001") hargs hlookup]
  exact eval_fpValid63 _ _ _

private theorem eval_fpValid_mload (yst : EvmState)
    (hiOffset loOffset : Nat)
    (hhi : hiOffset < 2 ^ 256) (hlo : loOffset < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 mainFuns [] yst
      (validCall hiOffset loOffset) =
      .ok (.vals
        [fpValidValue (loadWord yst.memory hiOffset)
          (loadWord yst.memory loOffset)]
        (afterTwoLoads yst hiOffset loOffset)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 mainFuns [] yst
          [.builtin .mload [.lit (.number hiOffset)],
            .builtin .mload [.lit (.number loOffset)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 mainFuns
          [("hi", loadWord yst.memory hiOffset),
            ("lo", loadWord yst.memory loOffset)]
          (afterTwoLoads yst hiOffset loOffset)
          [.var "hi", .var "lo"] := by
    norm_num at hhi hlo
    simp [Interp.evalArgs, Interp.evalExpr, afterTwoLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt hhi,
      Nat.mod_eq_of_lt hlo, VEnv.get]
  have hlookup : lookupFun mainFuns "\x001" =
      lookupFun [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock] "\x001" := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x001") hargs hlookup
  rw [validCall, hcall]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpValid (loadWord yst.memory hiOffset)
    (loadWord yst.memory loOffset) (afterTwoLoads yst hiOffset loOffset)]

private def validPair (hi0 lo0 hi1 lo1 : Nat) : Expr Op :=
  .builtin .and [validCall hi0 lo0, validCall hi1 lo1]

private def canonicalRaw : Expr Op :=
  .builtin .and [validPair 0 32 64 96, validPair 128 160 192 224]

private theorem eval_validPair (yst : EvmState)
    (hi0 lo0 hi1 lo1 : Nat)
    (hhi0 : hi0 < 2 ^ 256) (hlo0 : lo0 < 2 ^ 256)
    (hhi1 : hi1 < 2 ^ 256) (hlo1 : lo1 < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 66 mainFuns [] yst
      (validPair hi0 lo0 hi1 lo1) =
      .ok (.vals
        [fpValidValue (loadWord yst.memory hi0) (loadWord yst.memory lo0) &&&
          fpValidValue (loadWord yst.memory hi1) (loadWord yst.memory lo1)]
        (afterTwoLoads (afterTwoLoads yst hi1 lo1) hi0 lo0)) := by
  rw [validPair, Interp.evalExpr, Interp.evalArgs]
  rw [Interp.evalArgs, Interp.evalArgs]
  simp
  rw [eval_fpValid_mload63 yst hi1 lo1 hhi1 hlo1]
  simp
  rw [eval_fpValid_mload (afterTwoLoads yst hi1 lo1) hi0 lo0 hhi0 hlo0]
  simp [Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, afterTwoLoads,
    touchMemory_memory]

private theorem eval_validPair65 (yst : EvmState)
    (hi0 lo0 hi1 lo1 : Nat)
    (hhi0 : hi0 < 2 ^ 256) (hlo0 : lo0 < 2 ^ 256)
    (hhi1 : hi1 < 2 ^ 256) (hlo1 : lo1 < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 mainFuns [] yst
      (validPair hi0 lo0 hi1 lo1) =
      .ok (.vals
        [fpValidValue (loadWord yst.memory hi0) (loadWord yst.memory lo0) &&&
          fpValidValue (loadWord yst.memory hi1) (loadWord yst.memory lo1)]
        (afterTwoLoads (afterTwoLoads yst hi1 lo1) hi0 lo0)) := by
  rw [validPair, Interp.evalExpr, Interp.evalArgs]
  rw [Interp.evalArgs, Interp.evalArgs]
  simp
  rw [eval_fpValid_mload62 yst hi1 lo1 hhi1 hlo1]
  simp
  rw [eval_fpValid_mload63 (afterTwoLoads yst hi1 lo1)
    hi0 lo0 hhi0 hlo0]
  simp [Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, afterTwoLoads,
    touchMemory_memory]

private theorem eval_canonicalRaw (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns []
      (mainAfterPaddingReads yst)
      canonicalRaw =
      .ok (.vals [mainCanonicalValue yst]
        (mainAfterCanonicalReads yst)) := by
  rw [canonicalRaw, Interp.evalExpr, Interp.evalArgs]
  rw [Interp.evalArgs, Interp.evalArgs]
  simp
  rw [eval_validPair65 (mainAfterPaddingReads yst) 128 160 192 224
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  simp
  rw [eval_validPair _ 0 32 64 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  simp [Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, bin,
    mainCanonicalValue, mainAfterCanonicalReads, mainAfterPaddingReads,
    mainDecodedWord, afterTwoLoads, touchMemory_memory]

private theorem eval_mainCanonicalCondition (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 70 mainFuns []
      (mainAfterPaddingReads yst) mainCanonicalCondition =
      .ok (.vals [b2w (mainCanonicalValue yst = 0)]
        (mainAfterCanonicalReads yst)) := by
  have hshape : mainCanonicalCondition = .builtin .iszero [canonicalRaw] := by
    rfl
  rw [hshape, Interp.evalExpr, Interp.evalArgs,
    Interp.evalArgs]
  simp
  rw [eval_canonicalRaw yst]
  simp [Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, un, b2w]

private theorem mainCanonicalStmt_shape : mainCanonicalStmt =
    .cond mainCanonicalCondition
      [.exprStmt (.builtin .invalid [])] := by
  rfl

private theorem exec_invalidBlock (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70 mainFuns [] yst
      (.block [.exprStmt (.builtin .invalid [])]) =
      .ok ([], mainInvalidState yst, .halt) := by
  simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr,
    Interp.evalArgs, mainInvalidState, Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp, restore]

theorem exec_mainCanonical (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 71 mainFuns []
      (mainAfterPaddingReads yst) mainCanonicalStmt =
      if mainCanonicalValue yst = 0 then
        .ok ([], mainInvalidState (mainAfterCanonicalReads yst), .halt)
      else .ok ([], mainAfterCanonicalReads yst, .normal) := by
  rw [mainCanonicalStmt_shape, Interp.execStmt]
  rw [eval_mainCanonicalCondition]
  by_cases hcanonical : mainCanonicalValue yst = 0
  · have hbool : b2w (mainCanonicalValue yst = 0) = (1 : U256) := by
      simp [hcanonical, b2w]
    rw [if_pos hcanonical, hbool]
    change (if (1 : U256) =
        Dialect.zero Challenge.EvmProof.modexpExec.toDialect then
      .ok ([], mainAfterCanonicalReads yst, .normal)
    else Interp.execStmt Challenge.EvmProof.modexpExec 70 mainFuns []
      (mainAfterCanonicalReads yst)
      (.block [.exprStmt (.builtin .invalid [])])) = _
    rw [if_neg (by decide : (1 : U256) ≠
      Dialect.zero Challenge.EvmProof.modexpExec.toDialect)]
    exact exec_invalidBlock _
  · have hbool : b2w (mainCanonicalValue yst = 0) = (0 : U256) := by
      simp only [b2w]
      rw [if_neg (by simpa using hcanonical)]
    rw [if_neg (by simpa using hcanonical), hbool]
    change (if (0 : U256) =
        Dialect.zero Challenge.EvmProof.modexpExec.toDialect then
      .ok ([], mainAfterCanonicalReads yst, .normal)
    else Interp.execStmt Challenge.EvmProof.modexpExec 70 mainFuns []
      (mainAfterCanonicalReads yst)
      (.block [.exprStmt (.builtin .invalid [])])) = _
    rw [if_pos (by rfl : (0 : U256) =
      Dialect.zero Challenge.EvmProof.modexpExec.toDialect)]

theorem exec_mainCanonical_success (yst : EvmState)
    (hcanonical : mainCanonicalValue yst ≠ 0) :
    Interp.execStmt Challenge.EvmProof.modexpExec 71 mainFuns []
      (mainAfterPaddingReads yst) mainCanonicalStmt =
      .ok ([], mainAfterCanonicalReads yst, .normal) := by
  rw [exec_mainCanonical, if_neg hcanonical]

theorem exec_mainCanonical_reject (yst : EvmState)
    (hcanonical : mainCanonicalValue yst = 0) :
    Interp.execStmt Challenge.EvmProof.modexpExec 71 mainFuns []
      (mainAfterPaddingReads yst) mainCanonicalStmt =
      .ok ([], mainInvalidState (mainAfterCanonicalReads yst), .halt) := by
  rw [exec_mainCanonical, if_pos hcanonical]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
