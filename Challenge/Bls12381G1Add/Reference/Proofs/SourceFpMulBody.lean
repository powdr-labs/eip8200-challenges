import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulInput

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 100000

/-! # Complete frozen G1ADD `fpMul` wrapper -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpMulSourceBodyResultEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  restore (fpMulInitialEnv ahi alo bhi blo)
    (fpMulSourceAssignedEnv ahi alo bhi blo)

/-- Both parsed wrapper statements execute, calling local `fullMul` and the
locally verified Barrett reducer. -/
theorem exec_fpMulBody (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 67 fpMulFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody) =
    .ok (fpMulSourceBodyResultEnv ahi alo bhi blo, yst, .normal) := by
  rw [Interp.execStmt]
  change (do
    let (V, st, outcome) <- Interp.execStmts
      Challenge.YulProof.ClosedEvm.exec 66 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulBody
    return (restore (fpMulInitialEnv ahi alo bhi blo) V, st, outcome)) = _
  have hstmts :
      Interp.execStmts Challenge.YulProof.ClosedEvm.exec 66 fpMulBodyFuns
        (fpMulInitialEnv ahi alo bhi blo) yst fpMulBody =
      .ok (fpMulSourceAssignedEnv ahi alo bhi blo, yst, .normal) := by
    change Interp.execStmts Challenge.YulProof.ClosedEvm.exec 66 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst [fpMulStmt0, fpMulStmt1] = _
    exact Interp.execStmts_cons_normal (exec_fpMulStmt0 ahi alo bhi blo yst)
      (Interp.execStmts_cons_normal (exec_fpMulStmt1 ahi alo bhi blo yst) (by rfl))
  rw [hstmts]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
