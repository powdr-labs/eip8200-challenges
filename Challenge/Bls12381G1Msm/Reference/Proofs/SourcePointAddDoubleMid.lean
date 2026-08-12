import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleLate

set_option warningAsError true

/-! Existential firebreak from inversion through the doubling postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleMidCode : Block Op :=
  [pointAddDoubleInvStmt, pointAddDoubleLambdaStmt, pointAddDoubleX3Stmt] ++
    pointAddDoubleLateCode

theorem step_pointAddDoubleMid (yst : EvmState) (out left right : U256)
    (hhi : (pointAddDoubleDenResult yst out left right).1.toNat < 2 ^ 128) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddDoubleInvInitialEnv yst out left right)
        (pointAddDoubleDenArgsState yst out left right)
        pointAddDoubleMidCode Vend stend .normal := by
  obtain ⟨Vend, stend, hlate⟩ := step_pointAddDoubleLate yst out left right
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddDoubleMidCode, List.cons_append]
  exact Step.seqCons (step_pointAddDoubleInvStmt yst out left right hhi)
    (Step.seqCons (step_pointAddDoubleLambdaStmt yst out left right)
      (Step.seqCons (step_pointAddDoubleX3Stmt yst out left right) hlate))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
