import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFinitePostExec

set_option warningAsError true

/-! # Frozen G2ADD equal-x exceptional returns -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def clearReturnBody : Block Op :=
  [.exprStmt (.call "\x0022" []),
    .exprStmt (.builtin .ret [.lit (.number 0), .lit (.number 256)])]

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

private theorem eval_clear (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns [] yst
      (.call "\x0022" []) =
    .ok (.vals [] (mainFiniteClearState yst)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns [] yst [] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs [] yst [] := by rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0022") hargs (by rfl)]
  exact eval_clearPoint yst

private theorem step_clearReturnBody (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      clearReturnBody [] (mainFiniteClearReturnState yst) .halt := by
  have hclear := sound_evalExpr (eval_clear yst)
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainFiniteClearState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 256)])
      (.halt (mainFiniteClearReturnState yst)) :=
    Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl
  exact Step.seqCons (Step.exprStmt hclear)
    (Step.seqStop (Step.exprStmtHalt hret) (by decide))

def mainDoubleExceptionalBody : Block Op :=
  match mainFiniteStmt0 with
  | .cond _ body => body.take 2
  | _ => []

private theorem mainDoubleExceptionalBody_shape : mainDoubleExceptionalBody =
    [.cond (.builtin .iszero [
      .call "\x0013" [.lit (.number 128), .lit (.number 384)]])
      clearReturnBody,
     .cond (.call "\x0012" [.lit (.number 128)]) clearReturnBody] := by rfl

theorem step_mainDoubleExceptional_continue (yst : EvmState)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) mainDoubleExceptionalBody []
      (mainAfterDoubleYZero yst) .normal := by
  rw [mainDoubleExceptionalBody_shape]
  have heqZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst)
      (.builtin .iszero [
        .call "\x0013" [.lit (.number 128), .lit (.number 384)]])
      (.vals [b2w (mainDoubleYEq yst = 0)] (mainAfterDoubleYEq yst)) :=
    Step.builtinOk
      (Step.argsCons Step.argsNil
        (step_fp2EqLiteral [] _ 128 384)) rfl
  have hzero : b2w (mainDoubleYEq yst = 0) = (0 : U256) := by
    simp only [b2w]
    rw [if_neg (by simpa using hyeq)]
  have hfirst : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst)
      (.cond (.builtin .iszero [
        .call "\x0013" [.lit (.number 128), .lit (.number 384)]])
        clearReturnBody) [] (mainAfterDoubleYEq yst) .normal :=
    Step.ifFalse heqZero hzero
  have hsecond : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterDoubleYEq yst)
      (.cond (.call "\x0012" [.lit (.number 128)]) clearReturnBody)
      [] (mainAfterDoubleYZero yst) .normal :=
    Step.ifFalse
      (step_fp2ZeroLiteral [] (mainAfterDoubleYEq yst) 128) hyzero
  exact Step.seqCons hfirst (Step.seqCons hsecond Step.seqNil)

theorem step_mainDoubleExceptional_opposite (yst : EvmState)
    (hyeq : mainDoubleYEq yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) mainDoubleExceptionalBody []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt := by
  rw [mainDoubleExceptionalBody_shape]
  have heqZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst)
      (.builtin .iszero [
        .call "\x0013" [.lit (.number 128), .lit (.number 384)]])
      (.vals [b2w (mainDoubleYEq yst = 0)] (mainAfterDoubleYEq yst)) :=
    Step.builtinOk
      (Step.argsCons Step.argsNil
        (step_fp2EqLiteral [] _ 128 384)) rfl
  have hnonzero : b2w (mainDoubleYEq yst = 0) ≠ (0 : U256) := by
    simp [hyeq, b2w]
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] (mainAfterDoubleYEq yst) clearReturnBody []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr
      (step_clearReturnBody (mainAfterDoubleYEq yst))
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hhoist : hoist Challenge.EvmProof.modexpExec.toDialect
      clearReturnBody = [] := by rfl
  have hbody' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect clearReturnBody :: mainFuns)
      [] (mainAfterDoubleYEq yst) clearReturnBody []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt := by
    rw [hhoist]
    exact hbody
  exact Step.seqStop (Step.ifTrue heqZero hnonzero
    (by simpa [clearReturnBody, hoist, restore] using
      (Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hbody')))
    (by decide)

theorem step_mainDoubleExceptional_zeroY (yst : EvmState)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) mainDoubleExceptionalBody []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt := by
  rw [mainDoubleExceptionalBody_shape]
  have heqZero : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst)
      (.builtin .iszero [
        .call "\x0013" [.lit (.number 128), .lit (.number 384)]])
      (.vals [b2w (mainDoubleYEq yst = 0)] (mainAfterDoubleYEq yst)) :=
    Step.builtinOk
      (Step.argsCons Step.argsNil
        (step_fp2EqLiteral [] _ 128 384)) rfl
  have hzero : b2w (mainDoubleYEq yst = 0) = (0 : U256) := by
    simp only [b2w]
    rw [if_neg (by simpa using hyeq)]
  have hfirst : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst)
      (.cond (.builtin .iszero [
        .call "\x0013" [.lit (.number 128), .lit (.number 384)]])
        clearReturnBody) [] (mainAfterDoubleYEq yst) .normal :=
    Step.ifFalse heqZero hzero
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) []
      (fp2ReadState (mainAfterDoubleYEq yst) (128 : U256))
      clearReturnBody []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt := by
    simpa [mainAfterDoubleYZero] using
    YulEvmCompiler.Optimizer.Step.emptyScope_congr
      (step_clearReturnBody (mainAfterDoubleYZero yst))
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hhoist : hoist Challenge.EvmProof.modexpExec.toDialect
      clearReturnBody = [] := by rfl
  have hbody' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect clearReturnBody :: mainFuns)
      [] (fp2ReadState (mainAfterDoubleYEq yst) (128 : U256))
      clearReturnBody []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt := by
    rw [hhoist]
    exact hbody
  have hsecond := Step.ifTrue
    (step_fp2ZeroLiteral [] (mainAfterDoubleYEq yst) 128) hyzero
    (by simpa [clearReturnBody, hoist, restore] using
      (Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hbody'))
  exact Step.seqCons hfirst (Step.seqStop hsecond (by decide))

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
