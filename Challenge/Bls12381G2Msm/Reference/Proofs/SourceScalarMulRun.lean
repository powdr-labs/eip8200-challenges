import Challenge.Bls12381G2Msm.Reference.Proofs.SourceScalarMulLoop

set_option warningAsError true

/-! Complete structural execution and call transport for naive G2 scalar multiplication. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem appendNormalScalar {funs V st pre Vmid stmid suffix Vend
    stend outcome}
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

theorem step_scalarMulBody (yst stend : EvmState)
    (scalar point out : U256)
    (htrace : ScalarMulTrace scalar point out 256 scalarMulInitialBit
      (scalarMulInitState yst out) stend) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) yst scalarMulBody
      (scalarMulLoopEnv 0 scalar point out) stend .normal := by
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      scalarMulBodyFuns
      (scalarMulLoopEnv scalarMulInitialBit scalar point out)
      (scalarMulInitState yst out) [scalarMulStmt2]
      (scalarMulLoopEnv 0 scalar point out) stend .normal :=
    Step.seqCons (step_scalarMulFor scalar point out htrace) Step.seqNil
  have hrun := appendNormalScalar
    (step_scalarMulInit yst scalar point out) htail
  rw [scalarMulBody_eq_init_loop]
  exact hrun

theorem step_scalarMul (yst stend : EvmState) (scalar point out : U256)
    (htrace : ScalarMulTrace scalar point out 256 scalarMulInitialBit
      (scalarMulInitState yst out) stend) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect scalarMulFuns
      (scalarMulInitialEnv scalar point out) yst (.block scalarMulBody)
      (scalarMulInitialEnv scalar point out) stend .normal := by
  have hseq := step_scalarMulBody yst stend scalar point out htrace
  rw [← scalarMulBodyFuns_eq] at hseq
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect) hseq
  simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hblock

theorem step_scalarMul_of_args {funs V st argState args stend}
    (scalar point out : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [scalar, point, out] argState))
    (hlookup : lookupFun funs "\x0030" =
      some (scalarMulDecl, scalarMulFuns))
    (htrace : ScalarMulTrace scalar point out 256 scalarMulInitialBit
      (scalarMulInitState argState out) stend) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0030" args) (.vals [] stend) := by
  have hbody := step_scalarMul argState stend scalar point out htrace
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [scalarMulDecl, scalarMulInitialEnv] using hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
