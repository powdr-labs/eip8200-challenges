import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubBridge
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaBridge
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYMul
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalTail

set_option warningAsError true

/-! Existential firebreak from the unequal x subtractions through output stores. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalLateCode : Block Op :=
  [pointAddUnequalXSubStmt, pointAddUnequalDeltaInitStmt,
   pointAddUnequalDeltaStmt, pointAddUnequalYMulStmt] ++
    pointAddUnequalTailCode

theorem step_pointAddUnequalLate (yst : EvmState) (out left right : U256) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddUnequalX3Env yst out left right)
        (pointAddUnequalX3State yst out left right)
        pointAddUnequalLateCode Vend stend .normal := by
  obtain ⟨Vend, stend, htail⟩ := step_pointAddUnequalTail yst out left right
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddUnequalLateCode, List.cons_append]
  exact Step.seqCons (step_pointAddUnequalXSubStmt yst out left right)
    (Step.seqCons (step_pointAddUnequalDeltaInit yst out left right)
      (Step.seqCons
        (step_pointAddUnequalDeltaGeneric
          (pointAddUnequalDeltaContext yst out left right))
        (Step.seqCons (step_pointAddUnequalYMulStmt yst out left right) htail)))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
