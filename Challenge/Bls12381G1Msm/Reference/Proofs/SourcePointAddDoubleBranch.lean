import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleMid

set_option warningAsError true

/-! Relational composition of the equal-x, non-vertical doubling body. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_pointAddDoubleInvInit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleDenEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right)
      pointAddDoubleInvInitStmt (pointAddDoubleInvInitialEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right) .normal := by
  rw [pointAddDoubleInvInitStmt_eq]
  simpa [pointAddDoubleInvInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns)
      (V := pointAddDoubleDenEnv yst out left right)
      (st := pointAddDoubleDenArgsState yst out left right)
      (vars := ["\x00118", "\x00119"]))

def pointAddDoubleBranchCode : Block Op :=
  [pointAddXEqExceptionalStmt, pointAddDoubleXSqStmt,
   pointAddDoubleNum2Stmt, pointAddDoubleNum3Stmt,
   pointAddDoubleDenStmt, pointAddDoubleInvInitStmt] ++ pointAddDoubleMidCode

theorem pointAddDoubleBranchCode_eq :
    pointAddDoubleBranchCode = pointAddXEqMainBody := by rfl

theorem step_pointAddDoubleBranch (yst : EvmState)
    (out left right : U256)
    (hzero : pointAddYZeroValue yst out left right = 0)
    (hhi : (pointAddDoubleDenResult yst out left right).1.toNat < 2 ^ 128) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
        pointAddXEqMainBody Vend stend .normal := by
  obtain ⟨Vend, stend, hmid⟩ :=
    step_pointAddDoubleMid yst out left right hhi
  refine ⟨Vend, stend, ?_⟩
  rw [← pointAddDoubleBranchCode_eq, pointAddDoubleBranchCode,
    List.cons_append]
  exact Step.seqCons (step_pointAddYNonzero yst out left right hzero)
    (Step.seqCons (step_pointAddDoubleXSqStmt yst out left right)
      (Step.seqCons (step_pointAddDoubleNum2Stmt yst out left right)
        (Step.seqCons (step_pointAddDoubleNum3Stmt yst out left right)
          (Step.seqCons (step_pointAddDoubleDenStmt yst out left right)
            (Step.seqCons (step_pointAddDoubleInvInit yst out left right)
              hmid)))))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
