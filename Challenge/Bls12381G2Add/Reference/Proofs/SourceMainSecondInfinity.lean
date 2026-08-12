import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFirstInfinity

set_option warningAsError true

/-! # Frozen G2ADD second-infinity identity branch -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainSecondInfinityReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainValidatedState yst) 0 256 with
    halted := some (.ret, readBytes (mainValidatedState yst).memory 0 256) }

private theorem mainPointStmt6_shape : mainPointStmt6 =
    .cond (.var "\x00132")
      [.exprStmt (.builtin .ret
        [.lit (.number 0), .lit (.number 256)])] := by rfl

theorem step_mainSecondInfinity_return (yst : EvmState)
    (hsecond : mainInf2 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointStmt6
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt := by
  rw [mainPointStmt6_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x00132")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hzero : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.lit (.number 0)) (.vals [0] (mainValidatedState yst)) := Step.lit
  have hsize : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.lit (.number 256)) (.vals [256] (mainValidatedState yst)) := Step.lit
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 256)])
      (.halt (mainSecondInfinityReturnState yst)) :=
    Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil hsize) hzero) rfl
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt (.builtin .ret
        [.lit (.number 0), .lit (.number 256)])]
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt :=
    Step.seqStop (Step.exprStmtHalt hret) (by decide)
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt (.builtin .ret
          [.lit (.number 0), .lit (.number 256)])] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt (.builtin .ret
        [.lit (.number 0), .lit (.number 256)])]
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt := by
    simpa [hoist] using hseq
  have hblock := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  exact Step.ifTrue hcondition hsecond (by simpa [restore] using hblock)

theorem step_mainSecondInfinity_continue (yst : EvmState)
    (hsecond : mainInf2 yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainPointStmt6
      (mainPointEnv yst) (mainValidatedState yst) .normal := by
  rw [mainPointStmt6_shape]
  exact Step.ifFalse (Step.var (by rfl)) hsecond

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
