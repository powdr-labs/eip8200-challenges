import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleTail

set_option warningAsError true

/-! Existential firebreak from x subtraction through the doubling postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleLateCode : Block Op :=
  [pointAddDoubleXSubStmt, pointAddDoubleDeltaInitStmt,
   pointAddDoubleDeltaStmt, pointAddDoubleYMulStmt,
   pointAddDoubleYSubStmt] ++ pointAddDoublePostlude

theorem step_pointAddDoubleLate (yst : EvmState) (out left right : U256) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddDoubleX3Env yst out left right)
        (pointAddDoubleX3State yst out left right)
        pointAddDoubleLateCode Vend stend .normal := by
  obtain ⟨Vend, stend, htail⟩ := step_pointAddDoubleTail yst out left right
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddDoubleLateCode, List.cons_append]
  exact Step.seqCons (step_pointAddDoubleXSubStmt yst out left right)
    (Step.seqCons (step_pointAddDoubleDeltaInit yst out left right)
      (Step.seqCons
        (step_pointAddDoubleDeltaGeneric
          (pointAddDoubleDeltaContext yst out left right))
        (Step.seqCons (step_pointAddDoubleYMulStmt yst out left right) htail)))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
