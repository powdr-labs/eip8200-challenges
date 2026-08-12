import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalLambda
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalX3
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalLate

set_option warningAsError true

/-! Existential firebreak from unequal inversion through output stores. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalMidCode : Block Op :=
  [pointAddUnequalInvStmt, pointAddUnequalLambdaStmt,
   pointAddUnequalX3Stmt] ++ pointAddUnequalLateCode

theorem step_pointAddUnequalMid (yst : EvmState) (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddUnequalInvInitialEnv yst out left right)
        (pointAddUnequalNumeratorInputsState yst out left right)
        pointAddUnequalMidCode Vend stend .normal := by
  obtain ⟨Vend, stend, hlate⟩ := step_pointAddUnequalLate yst out left right
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddUnequalMidCode, List.cons_append]
  exact Step.seqCons (step_pointAddUnequalInvStmt yst out left right hhi)
    (Step.seqCons (step_pointAddUnequalLambdaStmt yst out left right)
      (Step.seqCons (step_pointAddUnequalX3Stmt yst out left right) hlate))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
