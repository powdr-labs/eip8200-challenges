import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteEqualExec

set_option warningAsError true

/-! # Frozen G2ADD unequal-x conditional execution -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainFiniteStmt1_shape_full : mainFiniteStmt1 =
    .cond (.builtin .iszero [
      .call "\x0013" [.lit (.number 0), .lit (.number 256)]])
      mainUnequalBody := by rfl

private theorem step_block_of_unequal {yst stend : EvmState}
    (h : ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainUnequalBody [] stend .normal) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      (.block mainUnequalBody) [] stend .normal := by
  have h' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) [] yst mainUnequalBody [] stend .normal :=
    YulEvmCompiler.Optimizer.Step.emptyScope_congr h
      (YulEvmCompiler.Optimizer.EmptyScopeRel.add mainFuns)
  have hhoist : hoist Challenge.EvmProof.modexpExec.toDialect
      mainUnequalBody = [] := by rfl
  have h'' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainUnequalBody :: mainFuns)
      [] yst mainUnequalBody [] stend .normal := by
    rw [hhoist]
    exact h'
  simpa [restore] using
    (Step.block (D := Challenge.EvmProof.modexpExec.toDialect) h'')

theorem step_mainFiniteUnequal_run (yst : EvmState)
    (hxeq : mainFiniteXEq2 yst = 0)
    (hinv : (fp2InvNorm (mainUnequalState1 yst) 2432).1.toNat < 2 ^ 128) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainAfterFiniteXEq1 yst) mainFiniteStmt1 []
      (mainUnequalFinalState yst) .normal := by
  rw [mainFiniteStmt1_shape_full]
  have hcond := step_mainFiniteEq2Condition yst
  have hnonzero : b2w (mainFiniteXEq2 yst = 0) ≠ (0 : U256) := by
    simp [hxeq, b2w]
  exact Step.ifTrue hcond hnonzero
    (step_block_of_unequal (step_mainUnequalBody yst hinv))

theorem step_mainFiniteUnequal_skip_after_double (yst : EvmState)
    (hxeq : mainDoubleXEq2 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainDoubleFinalState yst) mainFiniteStmt1 []
      (mainAfterDoubleXEq2 yst) .normal := by
  rw [mainFiniteStmt1_shape_full]
  have heq := step_fp2EqLiteral [] (mainDoubleFinalState yst) 0 256
  have hcond : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainDoubleFinalState yst)
      (.builtin .iszero [
        .call "\x0013" [.lit (.number 0), .lit (.number 256)]])
      (.vals [b2w (mainDoubleXEq2 yst = 0)]
        (mainAfterDoubleXEq2 yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil heq) rfl
  have hzero : b2w (mainDoubleXEq2 yst = 0) = (0 : U256) := by
    simp only [b2w]
    rw [if_neg (by simpa using hxeq)]
  exact Step.ifFalse hcond hzero

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
