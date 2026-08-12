import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFullIdentity
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFullUnequal
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFullEqual

set_option warningAsError true

/-! One total point-add execution boundary under explicit lawful memory facts. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- Facts that the enclosing fixed memory layout must supply for any finite
branch reached by `pointAdd`.  Keeping them conditional lets infinity inputs
avoid irrelevant finite-coordinate obligations. -/
structure PointAddReady (yst : EvmState) (out left right : U256) : Prop where
  unequalLeftX : pointAddLeftInfinityValue yst out left right = 0 →
    pointAddRightInfinityValue yst out left right = 0 →
    pointAddXEqValue yst out left right = 0 →
    Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right)
  unequalRightX : pointAddLeftInfinityValue yst out left right = 0 →
    pointAddRightInfinityValue yst out left right = 0 →
    pointAddXEqValue yst out left right = 0 →
    Fp.Canonical (pointAddUnequalRightXLimbs yst out left right)
  unequalState : pointAddLeftInfinityValue yst out left right = 0 →
    pointAddRightInfinityValue yst out left right = 0 →
    pointAddXEqValue yst out left right = 0 →
    pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right
  doubleLeftY : pointAddLeftInfinityValue yst out left right = 0 →
    pointAddRightInfinityValue yst out left right = 0 →
    pointAddXEqValue yst out left right ≠ 0 →
    pointAddYZeroValue yst out left right = 0 →
    Fp.Canonical (pointAddFiniteLeftYLimbs yst out left right)
  doubleRightY : pointAddLeftInfinityValue yst out left right = 0 →
    pointAddRightInfinityValue yst out left right = 0 →
    pointAddXEqValue yst out left right ≠ 0 →
    pointAddYZeroValue yst out left right = 0 →
    Fp.Canonical (pointAddFiniteRightYLimbs yst out left right)
  doubleInputY : pointAddLeftInfinityValue yst out left right = 0 →
    pointAddRightInfinityValue yst out left right = 0 →
    pointAddXEqValue yst out left right ≠ 0 →
    pointAddYZeroValue yst out left right = 0 →
    Fp.Canonical (pointAddDoubleLeftYLimbs yst out left right)
  doubleSum : pointAddLeftInfinityValue yst out left right = 0 →
    pointAddRightInfinityValue yst out left right = 0 →
    pointAddXEqValue yst out left right ≠ 0 →
    pointAddYZeroValue yst out left right = 0 →
    Fp.toField (pointAddFiniteLeftYLimbs yst out left right) +
      Fp.toField (pointAddFiniteRightYLimbs yst out left right) ≠ 0

theorem step_pointAddTotal (yst : EvmState) (out left right : U256)
    (hready : PointAddReady yst out left right) :
    ∃ Vend stend o,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out left right) yst pointAddBody Vend stend o ∧
      (o = .normal ∨ o = .leave) := by
  by_cases hleft : pointAddLeftInfinityValue yst out left right = 0
  · by_cases hright : pointAddRightInfinityValue yst out left right = 0
    · by_cases hxeq : pointAddXEqValue yst out left right = 0
      · obtain ⟨Vend, stend, hstep⟩ := step_pointAddFullUnequal_lawful
          yst out left right hleft hright hxeq
          (hready.unequalLeftX hleft hright hxeq)
          (hready.unequalRightX hleft hright hxeq)
          (hready.unequalState hleft hright hxeq)
        exact ⟨Vend, stend, .normal, hstep, Or.inl rfl⟩
      · by_cases hzero : pointAddYZeroValue yst out left right = 0
        · obtain ⟨Vend, stend, hstep⟩ := step_pointAddFullDouble_lawful
            yst out left right hleft hright hxeq
            (hready.doubleLeftY hleft hright hxeq hzero)
            (hready.doubleRightY hleft hright hxeq hzero)
            (hready.doubleInputY hleft hright hxeq hzero)
            (hready.doubleSum hleft hright hxeq hzero)
          exact ⟨Vend, stend, .leave, hstep, Or.inr rfl⟩
        · exact ⟨pointAddInitialEnv out left right,
            pointAddYZeroState yst out left right, .leave,
            step_pointAddFullVertical yst out left right hleft hright hxeq hzero,
            Or.inr rfl⟩
    · exact ⟨pointAddInitialEnv out left right,
        pointAddRightCopyState yst out left right, .leave,
        step_pointAddFullRightInfinity yst out left right hleft hright,
        Or.inr rfl⟩
  · exact ⟨pointAddInitialEnv out left right,
      pointAddLeftCopyState yst out left right, .leave,
      step_pointAddFullLeftInfinity yst out left right hleft,
      Or.inr rfl⟩

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
