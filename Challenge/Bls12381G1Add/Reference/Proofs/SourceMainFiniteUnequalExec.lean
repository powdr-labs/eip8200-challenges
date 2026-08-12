import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteUnequalState
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Frozen G1ADD unequal-x slope execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

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

theorem eval_fpSubLoads
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (aHi aLo bHi bLo : Nat)
    (haHi : aHi < 2 ^ 256) (haLo : aLo < 2 ^ 256)
    (hbHi : bHi < 2 ^ 256) (hbLo : bLo < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 ([] :: mainFuns) V yst
      (.call "\x005"
        [.builtin .mload [.lit (.number aHi)],
          .builtin .mload [.lit (.number aLo)],
          .builtin .mload [.lit (.number bHi)],
          .builtin .mload [.lit (.number bLo)]]) =
      .ok (.vals
        [(fpSubValue (loadWord yst.memory aHi) (loadWord yst.memory aLo)
          (loadWord yst.memory bHi) (loadWord yst.memory bLo)).1,
         (fpSubValue (loadWord yst.memory aHi) (loadWord yst.memory aLo)
          (loadWord yst.memory bHi) (loadWord yst.memory bLo)).2]
        (afterFourLoads yst aHi aLo bHi bLo)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 64 ([] :: mainFuns) V yst
          [.builtin .mload [.lit (.number aHi)],
            .builtin .mload [.lit (.number aLo)],
            .builtin .mload [.lit (.number bHi)],
            .builtin .mload [.lit (.number bLo)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
          [("ahi", loadWord yst.memory aHi),
            ("alo", loadWord yst.memory aLo),
            ("bhi", loadWord yst.memory bHi),
            ("blo", loadWord yst.memory bLo)]
          (afterFourLoads yst aHi aLo bHi bLo)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    norm_num at haHi haLo hbHi hbLo
    simp [Interp.evalArgs, Interp.evalExpr, afterFourLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt haHi,
      Nat.mod_eq_of_lt haLo, Nat.mod_eq_of_lt hbHi,
      Nat.mod_eq_of_lt hbLo, VEnv.get]
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x005") hargs (show lookupFun ([] :: mainFuns) "\x005" =
      lookupFun mainFuns "\x005" by rfl)]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpSub _ _ _ _ _

private theorem exec_stmt0 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteUnequalConditionState yst)
      mainFiniteUnequalStmt0 =
    .ok (mainFiniteUnequalEnv1 yst,
      mainFiniteUnequalNumeratorArgsState yst, .normal) := by
  rw [show mainFiniteUnequalStmt0 =
    .letDecl ["\x00108", "\x00109"]
      (some (.call "\x005"
        [.builtin .mload [.lit (.number 192)],
          .builtin .mload [.lit (.number 224)],
          .builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])) by rfl]
  rw [Interp.execStmt, eval_fpSubLoads (mainFiniteEnv yst)
    (mainFiniteUnequalConditionState yst) 192 224 64 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [mainFiniteUnequalConditionState_loadWord yst 192 (by norm_num),
    mainFiniteUnequalConditionState_loadWord yst 224 (by norm_num),
    mainFiniteUnequalConditionState_loadWord yst 64 (by norm_num),
    mainFiniteUnequalConditionState_loadWord yst 96 (by norm_num)]
  rfl

private theorem exec_stmt1 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 ([] :: mainFuns)
      (mainFiniteUnequalEnv1 yst) (mainFiniteUnequalNumeratorArgsState yst)
      mainFiniteUnequalStmt1 =
    .ok (mainFiniteUnequalEnv2 yst,
      mainFiniteUnequalDenominatorArgsState yst, .normal) := by
  rw [show mainFiniteUnequalStmt1 =
    .letDecl ["\x00110", "\x00111"]
      (some (.call "\x005"
        [.builtin .mload [.lit (.number 128)],
          .builtin .mload [.lit (.number 160)],
          .builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)]])) by rfl]
  rw [Interp.execStmt, eval_fpSubLoads (mainFiniteUnequalEnv1 yst)
    (mainFiniteUnequalNumeratorArgsState yst) 128 160 0 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [mainFiniteUnequalNumeratorArgsState_loadWord yst 128 (by norm_num),
    mainFiniteUnequalNumeratorArgsState_loadWord yst 160 (by norm_num),
    mainFiniteUnequalNumeratorArgsState_loadWord yst 0 (by norm_num),
    mainFiniteUnequalNumeratorArgsState_loadWord yst 32 (by norm_num)]
  rfl

private theorem exec_stmt2 (yst : EvmState)
    (hhi : (mainFiniteUnequalDenominatorWords yst).1.toNat < 2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 ([] :: mainFuns)
      (mainFiniteUnequalEnv2 yst) (mainFiniteUnequalDenominatorArgsState yst)
      mainFiniteUnequalStmt2 =
    .ok (mainFiniteUnequalEnv3 yst, mainFiniteUnequalState1 yst,
      .normal) := by
  let den := mainFiniteUnequalDenominatorWords yst
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67
      ([] :: mainFuns) (mainFiniteUnequalEnv2 yst)
      (mainFiniteUnequalDenominatorArgsState yst)
      [.var "\x00110", .var "\x00111"] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns
      [("hi", den.1), ("lo", den.2)]
      (mainFiniteUnequalDenominatorArgsState yst) [.var "hi", .var "lo"] := by
    rfl
  rw [show mainFiniteUnequalStmt2 =
    .letDecl ["\x00112", "\x00113"]
      (some (.call "\x0010" [.var "\x00110", .var "\x00111"])) by rfl,
    Interp.execStmt,
    Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x0010") hargs
      (show lookupFun ([] :: mainFuns) "\x0010" =
        lookupFun mainFuns "\x0010" by rfl)]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpInv den.1 den.2 (mainFiniteUnequalDenominatorArgsState yst) hhi]
  rfl

private theorem exec_stmt3 (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 69 ([] :: mainFuns)
      (mainFiniteUnequalEnv3 yst) (mainFiniteUnequalState1 yst)
      mainFiniteUnequalStmt3 =
    .ok (mainFiniteUnequalEnv4 yst, mainFiniteUnequalFinalState yst,
      .normal) := by
  let num := mainFiniteUnequalNumeratorWords yst
  let denInv := mainFiniteUnequalDenInvWords yst
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67
      ([] :: mainFuns) (mainFiniteUnequalEnv3 yst)
      (mainFiniteUnequalState1 yst)
      [.var "\x00108", .var "\x00109",
        .var "\x00112", .var "\x00113"] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns
      [("ahi", num.1), ("alo", num.2),
        ("bhi", denInv.1), ("blo", denInv.2)]
      (mainFiniteUnequalState1 yst)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  rw [show mainFiniteUnequalStmt3 =
    .assign ["\x0098", "\x0099"]
      (.call "\x009"
        [.var "\x00108", .var "\x00109",
          .var "\x00112", .var "\x00113"]) by rfl,
    Interp.execStmt,
    Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x009") hargs
      (show lookupFun ([] :: mainFuns) "\x009" =
        lookupFun mainFuns "\x009" by rfl)]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul num.1 num.2 denInv.1 denInv.2
    (mainFiniteUnequalState1 yst)]
  rfl

theorem step_mainFiniteUnequalBody (yst : EvmState)
    (hhi : (mainFiniteUnequalDenominatorWords yst).1.toNat < 2 ^ 128) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteUnequalConditionState yst)
      mainFiniteUnequalBody (mainFiniteUnequalEnv4 yst)
      (mainFiniteUnequalFinalState yst) .normal := by
  rw [mainFiniteUnequalBody_eq]
  exact Step.seqCons (sound_execStmt (exec_stmt0 yst))
    (Step.seqCons (sound_execStmt (exec_stmt1 yst))
      (Step.seqCons (sound_execStmt (exec_stmt2 yst hhi))
        (Step.seqCons (sound_execStmt (exec_stmt3 yst)) Step.seqNil)))

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).1
    _ _ _ _ _ h

private def unequalXEqCall : Expr Op :=
  .call "\x003"
    [.builtin .mload [.lit (.number 0)],
      .builtin .mload [.lit (.number 32)],
      .builtin .mload [.lit (.number 128)],
      .builtin .mload [.lit (.number 160)]]

private theorem unequalXEq_eval (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst) unequalXEqCall
      (.vals [mainFiniteXEqValue yst]
        (mainFiniteUnequalConditionState yst)) := by
  apply sound_evalExpr
  have h := eval_fpEqLoads mainFuns (mainFiniteEnv yst)
    (mainFiniteXEqArgsState yst) 0 32 128 160
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
  rw [mainFiniteXEqArgsState_loadWord yst 0 (by norm_num),
    mainFiniteXEqArgsState_loadWord yst 32 (by norm_num),
    mainFiniteXEqArgsState_loadWord yst 128 (by norm_num),
    mainFiniteXEqArgsState_loadWord yst 160 (by norm_num)] at h
  exact h

private theorem mainFiniteUnequalStmt_shape : mainFiniteUnequalStmt =
    .cond (.builtin .iszero [unequalXEqCall]) mainFiniteUnequalBody := by
  rfl

private theorem mainFiniteUnequalBody_hoist :
    hoist Challenge.EvmProof.modexpExec.toDialect mainFiniteUnequalBody = [] := by
  rfl

/-- Exact top-level index-27 execution for unequal x coordinates. -/
theorem step_mainFiniteUnequal (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 0)
    (hhi : (mainFiniteUnequalDenominatorWords yst).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteUnequalStmt (mainFiniteUnequalResultEnv yst)
      (mainFiniteUnequalFinalState yst) .normal := by
  rw [mainFiniteUnequalStmt_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      (.builtin .iszero [unequalXEqCall])
      (.vals [b2w (mainFiniteXEqValue yst = 0)]
        (mainFiniteUnequalConditionState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil (unequalXEq_eval yst)) rfl
  have hseq := step_mainFiniteUnequalBody yst hhi
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainFiniteUnequalBody ::
        mainFuns) (mainFiniteEnv yst) (mainFiniteUnequalConditionState yst)
      mainFiniteUnequalBody (mainFiniteUnequalEnv4 yst)
      (mainFiniteUnequalFinalState yst) .normal := by
    rw [mainFiniteUnequalBody_hoist]
    exact hseq
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  have hnonzero : b2w (mainFiniteXEqValue yst = 0) ≠
      Challenge.EvmProof.modexpExec.toDialect.zero := by
    rw [hxeq]
    decide
  exact Step.ifTrue hcondition hnonzero (by
    simpa only [mainFiniteUnequalResultEnv] using hblock)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
