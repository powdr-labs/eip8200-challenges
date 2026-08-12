import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDefs

set_option warningAsError true

/-! # Frozen G2ADD finite x-coordinate classification -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def finiteEqCall : Expr Op :=
  .call "\x0013" [.lit (.number 0), .lit (.number 256)]

private theorem mainFiniteStmt0_shape : mainFiniteStmt0 =
    .cond finiteEqCall
      (match mainFiniteStmt0 with | .cond _ body => body | _ => []) := by rfl

private theorem mainFiniteStmt1_shape : mainFiniteStmt1 =
    .cond (.builtin .iszero [finiteEqCall])
      (match mainFiniteStmt1 with | .cond _ body => body | _ => []) := by rfl

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

private theorem eval_finiteEqCall
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns V yst
      finiteEqCall =
    .ok (.vals [fp2EqValue yst 0 256] (fp2EqReadState yst 0 256)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns V yst
          [.lit (.number 0), .lit (.number 256)] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
          [("a", (0 : U256)), ("b", (256 : U256))] yst
          [.var "a", .var "b"] := by rfl
  rw [finiteEqCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0013") hargs (by rfl)]
  exact eval_fp2Eq 0 256 yst

theorem step_mainFiniteEq1 (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) finiteEqCall
      (.vals [mainFiniteXEq1 yst] (mainAfterFiniteXEq1 yst)) := by
  exact sound_evalExpr (eval_finiteEqCall [] (mainValidatedState yst))

theorem step_mainFiniteEqual_skip (yst : EvmState)
    (hxeq : mainFiniteXEq1 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteStmt0 []
      (mainAfterFiniteXEq1 yst) .normal := by
  rw [mainFiniteStmt0_shape]
  exact Step.ifFalse (step_mainFiniteEq1 yst) hxeq

theorem step_mainFiniteEq2Condition (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) (.builtin .iszero [finiteEqCall])
      (.vals [b2w (mainFiniteXEq2 yst = 0)]
        (mainAfterFiniteXEq2 yst)) := by
  have heq : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) finiteEqCall
      (.vals [mainFiniteXEq2 yst] (mainAfterFiniteXEq2 yst)) := by
    exact sound_evalExpr (eval_finiteEqCall [] (mainAfterFiniteXEq1 yst))
  exact Step.builtinOk (Step.argsCons Step.argsNil heq) rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
