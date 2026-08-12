import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalEntry
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalLawful

set_option warningAsError true

/-! Complete finite, unequal-x suffix of the frozen point-add helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddFiniteUnequalCode : Block Op :=
  pointAddStmt5 :: pointAddUnequalBranchCode

theorem pointAddFiniteUnequalCode_eq :
    pointAddFiniteUnequalCode = pointAddBody.drop 5 := by rfl

theorem step_pointAddFiniteUnequal_lawful (yst : EvmState)
    (out left right : U256)
    (hxeq : pointAddXEqValue yst out left right = 0)
    (hleft : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hright : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right))
    (hstate : pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out left right)
        (pointAddFiniteState yst out left right)
        pointAddFiniteUnequalCode Vend stend .normal := by
  obtain ⟨Vend, stend, hbranch⟩ :=
    step_pointAddUnequalBranch_lawful yst out left right hleft hright hstate
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddFiniteUnequalCode]
  exact Step.seqCons (step_pointAddXUnequal yst out left right hxeq) hbranch

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
