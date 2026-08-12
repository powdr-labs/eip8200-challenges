import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFiniteEntry
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFiniteUnequal

set_option warningAsError true

/-! Complete frozen point-add execution for two finite, unequal-x points. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem step_pointAddFullUnequal_lawful (yst : EvmState)
    (out left right : U256)
    (hleftFinite : pointAddLeftInfinityValue yst out left right = 0)
    (hrightFinite : pointAddRightInfinityValue yst out left right = 0)
    (hxeq : pointAddXEqValue yst out left right = 0)
    (hleft : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hright : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right))
    (hstate : pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out left right) yst pointAddBody
        Vend stend .normal := by
  obtain ⟨Vend, stend, hsuffix⟩ :=
    step_pointAddFiniteUnequal_lawful yst out left right hxeq hleft hright
      hstate
  refine ⟨Vend, stend, ?_⟩
  rw [show pointAddBody = pointAddFiniteEntryCode ++
      pointAddFiniteUnequalCode by rfl]
  exact step_pointAddUnequal_appendNormal
    (step_pointAddFiniteEntry yst out left right hleftFinite hrightFinite)
    hsuffix

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
