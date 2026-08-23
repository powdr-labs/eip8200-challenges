import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleState
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Frozen G1ADD equal-point doubling-slope execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainFiniteDoubleStmt0_shape : mainFiniteDoubleStmt0 =
    .letDecl ["\x00100", "\x00101"]
      (some (.call "\x009"
        [.builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)],
          .builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)]])) := by
  rfl

/-- Exact execution of the source multiplication computing `x²`. -/
private theorem exec_mainFiniteDoubleStmt0 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      mainFiniteDoubleStmt0 =
    .ok (mainFiniteDoubleEnv1 yst, mainFiniteDoubleState1 yst, .normal) := by
  let x := mainFiniteDoubleXWords yst
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 ([] :: mainFuns)
          (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
          [.builtin .mload [.lit (.number 0)],
            .builtin .mload [.lit (.number 32)],
            .builtin .mload [.lit (.number 0)],
            .builtin .mload [.lit (.number 32)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns
          [("ahi", x.1), ("alo", x.2), ("bhi", x.1), ("blo", x.2)]
          (mainFiniteDoubleXSqArgsState yst)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    dsimp only [x, mainFiniteDoubleXWords]
    simp [Interp.evalArgs, Interp.evalExpr, EVM.litValue,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, mainFiniteDoubleXSqArgsState, afterFourLoads,
      mainFiniteYZeroArgsState_loadWord, VEnv.get]
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs (show lookupFun ([] :: mainFuns) "\x009" =
      lookupFun mainFuns "\x009" by rfl)
  rw [mainFiniteDoubleStmt0_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul x.1 x.2 x.1 x.2 (mainFiniteDoubleXSqArgsState yst)]
  rfl

private theorem mainFiniteDoubleStmt1_shape : mainFiniteDoubleStmt1 =
    .letDecl ["\x00102", "\x00103"]
      (some (.call "\x004"
        [.var "\x00100", .var "\x00101",
          .var "\x00100", .var "\x00101"])) := by
  rfl

private theorem exec_mainFiniteDoubleStmt1 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 ([] :: mainFuns)
      (mainFiniteDoubleEnv1 yst) (mainFiniteDoubleState1 yst)
      mainFiniteDoubleStmt1 =
    .ok (mainFiniteDoubleEnv2 yst, mainFiniteDoubleState1 yst, .normal) := by
  let xSq := mainFiniteDoubleXSqWords yst
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 ([] :: mainFuns)
          (mainFiniteDoubleEnv1 yst) (mainFiniteDoubleState1 yst)
          [.var "\x00100", .var "\x00101",
            .var "\x00100", .var "\x00101"] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 mainFuns
          [("ahi", xSq.1), ("alo", xSq.2),
            ("bhi", xSq.1), ("blo", xSq.2)]
          (mainFiniteDoubleState1 yst)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs (show lookupFun ([] :: mainFuns) "\x004" =
      lookupFun mainFuns "\x004" by rfl)
  rw [mainFiniteDoubleStmt1_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpAdd xSq.1 xSq.2 xSq.1 xSq.2]
  rfl

private theorem mainFiniteDoubleStmt2_shape : mainFiniteDoubleStmt2 =
    .assign ["\x00102", "\x00103"]
      (.call "\x004"
        [.var "\x00102", .var "\x00103",
          .var "\x00100", .var "\x00101"]) := by
  rfl

private theorem exec_mainFiniteDoubleStmt2 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 ([] :: mainFuns)
      (mainFiniteDoubleEnv2 yst) (mainFiniteDoubleState1 yst)
      mainFiniteDoubleStmt2 =
    .ok (mainFiniteDoubleEnv3 yst, mainFiniteDoubleState1 yst, .normal) := by
  let twice := mainFiniteDoubleTwiceWords yst
  let xSq := mainFiniteDoubleXSqWords yst
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 ([] :: mainFuns)
          (mainFiniteDoubleEnv2 yst) (mainFiniteDoubleState1 yst)
          [.var "\x00102", .var "\x00103",
            .var "\x00100", .var "\x00101"] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 mainFuns
          [("ahi", twice.1), ("alo", twice.2),
            ("bhi", xSq.1), ("blo", xSq.2)]
          (mainFiniteDoubleState1 yst)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs (show lookupFun ([] :: mainFuns) "\x004" =
      lookupFun mainFuns "\x004" by rfl)
  rw [mainFiniteDoubleStmt2_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpAdd twice.1 twice.2 xSq.1 xSq.2]
  rfl

private theorem mainFiniteDoubleStmt3_shape : mainFiniteDoubleStmt3 =
    .letDecl ["\x00104", "\x00105"]
      (some (.call "\x004"
        [.builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)],
          .builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])) := by
  rfl

private theorem exec_mainFiniteDoubleStmt3 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 ([] :: mainFuns)
      (mainFiniteDoubleEnv3 yst) (mainFiniteDoubleState1 yst)
      mainFiniteDoubleStmt3 =
    .ok (mainFiniteDoubleEnv4 yst, mainFiniteDoubleDenArgsState yst,
      .normal) := by
  let y := mainFiniteDoubleYWords yst
  have hload64 : loadWord (mainFiniteDoubleState1 yst).memory 64 = y.1 := by
    rw [mainFiniteDoubleState1]
    rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ 64 (by norm_num)]
    rw [mainFiniteDoubleXSqArgsState]
    simpa [y, mainFiniteDoubleYWords] using
      mainFiniteYZeroArgsState_loadWord yst 64 (by norm_num)
  have hload96 : loadWord (mainFiniteDoubleState1 yst).memory 96 = y.2 := by
    rw [mainFiniteDoubleState1]
    rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ 96 (by norm_num)]
    rw [mainFiniteDoubleXSqArgsState]
    simpa [y, mainFiniteDoubleYWords] using
      mainFiniteYZeroArgsState_loadWord yst 96 (by norm_num)
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 ([] :: mainFuns)
          (mainFiniteDoubleEnv3 yst) (mainFiniteDoubleState1 yst)
          [.builtin .mload [.lit (.number 64)],
            .builtin .mload [.lit (.number 96)],
            .builtin .mload [.lit (.number 64)],
            .builtin .mload [.lit (.number 96)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 mainFuns
          [("ahi", y.1), ("alo", y.2), ("bhi", y.1), ("blo", y.2)]
          (mainFiniteDoubleDenArgsState yst)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, EVM.litValue,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, mainFiniteDoubleDenArgsState, afterFourLoads,
      hload64, hload96, VEnv.get]
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs (show lookupFun ([] :: mainFuns) "\x004" =
      lookupFun mainFuns "\x004" by rfl)
  rw [mainFiniteDoubleStmt3_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpAdd y.1 y.2 y.1 y.2]
  rfl

private theorem mainFiniteDoubleStmt4_shape : mainFiniteDoubleStmt4 =
    .letDecl ["\x00106", "\x00107"]
      (some (.call "\x0010" [.var "\x00104", .var "\x00105"])) := by
  rfl

private theorem exec_mainFiniteDoubleStmt4 (yst : EvmState)
    (hhi : (mainFiniteDoubleDenominatorWords yst).1.toNat < 2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 ([] :: mainFuns)
      (mainFiniteDoubleEnv4 yst) (mainFiniteDoubleDenArgsState yst)
      mainFiniteDoubleStmt4 =
    .ok (mainFiniteDoubleEnv5 yst, mainFiniteDoubleState2 yst, .normal) := by
  let den := mainFiniteDoubleDenominatorWords yst
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 ([] :: mainFuns)
          (mainFiniteDoubleEnv4 yst) (mainFiniteDoubleDenArgsState yst)
          [.var "\x00104", .var "\x00105"] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns
          [("hi", den.1), ("lo", den.2)]
          (mainFiniteDoubleDenArgsState yst) [.var "hi", .var "lo"] := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0010") hargs (show lookupFun ([] :: mainFuns) "\x0010" =
      lookupFun mainFuns "\x0010" by rfl)
  rw [mainFiniteDoubleStmt4_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpInv den.1 den.2 (mainFiniteDoubleDenArgsState yst) hhi]
  rfl

private theorem mainFiniteDoubleStmt5_shape : mainFiniteDoubleStmt5 =
    .assign ["\x0098", "\x0099"]
      (.call "\x009"
        [.var "\x00102", .var "\x00103",
          .var "\x00106", .var "\x00107"]) := by
  rfl

private theorem exec_mainFiniteDoubleStmt5 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 ([] :: mainFuns)
      (mainFiniteDoubleEnv5 yst) (mainFiniteDoubleState2 yst)
      mainFiniteDoubleStmt5 =
    .ok (mainFiniteDoubleEnv6 yst, mainFiniteDoubleFinalState yst,
      .normal) := by
  let num := mainFiniteDoubleNumeratorWords yst
  let denInv := mainFiniteDoubleDenInvWords yst
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 ([] :: mainFuns)
          (mainFiniteDoubleEnv5 yst) (mainFiniteDoubleState2 yst)
          [.var "\x00102", .var "\x00103",
            .var "\x00106", .var "\x00107"] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns
          [("ahi", num.1), ("alo", num.2),
            ("bhi", denInv.1), ("blo", denInv.2)]
          (mainFiniteDoubleState2 yst)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs (show lookupFun ([] :: mainFuns) "\x009" =
      lookupFun mainFuns "\x009" by rfl)
  rw [mainFiniteDoubleStmt5_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul num.1 num.2 denInv.1 denInv.2
    (mainFiniteDoubleState2 yst)]
  rfl

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).2.2.1
    funs V st stmt V' st' outcome h

/-- The complete six-statement source doubling-slope schedule executes to the
exact lambda words. -/
theorem step_mainFiniteDoubleBody (yst : EvmState)
    (hhi : (mainFiniteDoubleDenominatorWords yst).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      mainFiniteDoubleBody (mainFiniteDoubleEnv6 yst)
      (mainFiniteDoubleFinalState yst) .normal := by
  rw [mainFiniteDoubleBody_eq]
  exact Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt0 yst))
    (Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt1 yst))
      (Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt2 yst))
        (Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt3 yst))
          (Step.seqCons
            (sound_execStmt (exec_mainFiniteDoubleStmt4 yst hhi))
            (Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt5 yst))
              Step.seqNil)))))

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
