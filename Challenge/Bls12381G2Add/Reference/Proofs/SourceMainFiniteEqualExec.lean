import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteExceptional

set_option warningAsError true

/-! # Complete frozen G2ADD equal-x branch execution -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainEqualBody : Block Op :=
  match mainFiniteStmt0 with | .cond _ body => body | _ => []

private theorem mainEqualBody_decompose : mainEqualBody =
    mainDoubleExceptionalBody ++ mainDoubleBody := by rfl

private theorem mainFiniteStmt0_shape_full : mainFiniteStmt0 =
    .cond (.call "\x0013" [.lit (.number 0), .lit (.number 256)])
      mainEqualBody := by rfl

private theorem step_append_normal
    {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st pre
      Vmid stmid .normal)
    (hs : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil => cases hp; simpa using hs
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht hs)
    | seqStop _ hn => exact (hn rfl).elim

private theorem step_append_halt
    {funs V st pre Vend stend suffix}
    (hp : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st pre
      Vend stend .halt) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend .halt := by
  induction pre generalizing V st Vend stend with
  | nil => cases hp
  | cons head rest ih =>
    cases hp with
    | seqCons hh ht => simpa using Step.seqCons hh (ih ht)
    | seqStop hh hn => exact Step.seqStop hh hn

private theorem step_block_of_stmts {yst stend : EvmState} {outcome}
    (h : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainEqualBody [] stend outcome) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      (.block mainEqualBody) [] stend outcome := by
  have h' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] yst mainEqualBody [] stend outcome :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr h
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hhoist : hoist Challenge.EvmProof.modexpExec.toDialect
      mainEqualBody = [] := by rfl
  have h'' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainEqualBody :: mainFuns)
      [] yst mainEqualBody [] stend outcome := by
    rw [hhoist]
    exact h'
  simpa [restore] using
    (Step.block (D := Challenge.EvmProof.modexpExec.toDialect) h'')

theorem step_mainFiniteEqual_double (yst : EvmState)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst = 0)
    (hinv : (fp2InvNorm (mainDoubleState3 yst) 2432).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteStmt0 []
      (mainDoubleFinalState yst) .normal := by
  rw [mainFiniteStmt0_shape_full]
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) mainEqualBody []
      (mainDoubleFinalState yst) .normal := by
    rw [mainEqualBody_decompose]
    exact step_append_normal
      (step_mainDoubleExceptional_continue yst hyeq hyzero)
      (step_mainDoubleBody yst hinv)
  exact Step.ifTrue (step_mainFiniteEq1 yst) hxeq
    (step_block_of_stmts hbody)

theorem step_mainFiniteEqual_opposite (yst : EvmState)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteStmt0 []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt := by
  rw [mainFiniteStmt0_shape_full]
  have hprefix := step_mainDoubleExceptional_opposite yst hyeq
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) mainEqualBody []
      (mainFiniteClearReturnState (mainAfterDoubleYEq yst)) .halt := by
    rw [mainEqualBody_decompose]
    exact step_append_halt hprefix
  exact Step.ifTrue (step_mainFiniteEq1 yst) hxeq
    (step_block_of_stmts hbody)

theorem step_mainFiniteEqual_zeroY (yst : EvmState)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainValidatedState yst) mainFiniteStmt0 []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt := by
  rw [mainFiniteStmt0_shape_full]
  have hprefix := step_mainDoubleExceptional_zeroY yst hyeq hyzero
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) mainEqualBody []
      (mainFiniteClearReturnState (mainAfterDoubleYZero yst)) .halt := by
    rw [mainEqualBody_decompose]
    exact step_append_halt hprefix
  exact Step.ifTrue (step_mainFiniteEq1 yst) hxeq
    (step_block_of_stmts hbody)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
