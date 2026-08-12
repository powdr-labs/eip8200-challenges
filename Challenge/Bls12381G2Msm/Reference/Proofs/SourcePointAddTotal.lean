import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddExceptionalRun
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvMemory

set_option warningAsError true

/-! Total G2 point-add execution under an explicit finite-memory invariant. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

structure PointAddMemoryInvariant (yst : EvmState)
    (out left right : U256) : Prop where
  doubleDenCanonical :
    pointZeroValue (pointAddLeftPointerState yst out left right)
        (pointAddLeftPointer yst out left right) = 0 →
    pointZeroValue (pointAddRightPointerState yst out left right)
        (pointAddRightPointer yst out left right) = 0 →
    pointAddEqValue (pointAddFiniteStart yst out left right) ≠ 0 →
    pointAddDoubleYZero
        (pointAddDoubleState1 (pointAddFiniteStart yst out left right)) = 0 →
    Fp2.Canonical (fp2At
      (pointAddDoubleState6 (pointAddFiniteStart yst out left right)) 2432)
  doubleEqStable :
    pointZeroValue (pointAddLeftPointerState yst out left right)
        (pointAddLeftPointer yst out left right) = 0 →
    pointZeroValue (pointAddRightPointerState yst out left right)
        (pointAddRightPointer yst out left right) = 0 →
    pointAddEqValue (pointAddFiniteStart yst out left right) ≠ 0 →
    pointAddDoubleYZero
        (pointAddDoubleState1 (pointAddFiniteStart yst out left right)) = 0 →
    pointAddEqValue
      (pointAddDoubleFinalState (pointAddFiniteStart yst out left right)) ≠ 0
  unequalDenCanonical :
    pointZeroValue (pointAddLeftPointerState yst out left right)
        (pointAddLeftPointer yst out left right) = 0 →
    pointZeroValue (pointAddRightPointerState yst out left right)
        (pointAddRightPointer yst out left right) = 0 →
    pointAddEqValue (pointAddFiniteStart yst out left right) = 0 →
    Fp2.Canonical (fp2At
      (pointAddUnequalState2 (pointAddUnequalAfterEqualSkip
        (pointAddFiniteStart yst out left right))) 2432)
  unequalEqStable :
    pointZeroValue (pointAddLeftPointerState yst out left right)
        (pointAddLeftPointer yst out left right) = 0 →
    pointZeroValue (pointAddRightPointerState yst out left right)
        (pointAddRightPointer yst out left right) = 0 →
    pointAddEqValue (pointAddFiniteStart yst out left right) = 0 →
    pointAddEqValue (pointAddUnequalAfterEqualSkip
      (pointAddFiniteStart yst out left right)) = 0

private theorem invNormBound_of_canonical (st : EvmState)
    (hcanonical : Fp2.Canonical (fp2At st 2432)) :
    (fp2InvNorm st 2432).1.toNat < 2 ^ 128 := by
  exact Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvNorm_hi_lt_of_input
    st 2432 hcanonical (by decide) (by decide)

theorem step_pointAddTotal (yst : EvmState) (out left right : U256)
    (hready : PointAddMemoryInvariant yst out left right) :
    ∃ stend outcome,
      ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
        (pointAddInitialEnv out left right) yst (.block pointAddBody)
        (pointAddInitialEnv out left right) stend outcome ∧
      (outcome = .normal ∨ outcome = .leave) := by
  by_cases hleft : pointZeroValue
      (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) = 0
  · by_cases hright : pointZeroValue
        (pointAddRightPointerState yst out left right)
        (pointAddRightPointer yst out left right) = 0
    · by_cases heq : pointAddEqValue
          (pointAddFiniteStart yst out left right) = 0
      · have heq2 := hready.unequalEqStable hleft hright heq
        have hhi := invNormBound_of_canonical _
          (hready.unequalDenCanonical hleft hright heq)
        exact ⟨pointAddFiniteUnequalFinal
            (pointAddFiniteStart yst out left right), .normal,
          step_pointAddUnequal yst out left right hleft hright heq heq2 hhi,
          Or.inl rfl⟩
      · by_cases hy : pointAddDoubleYZero
            (pointAddDoubleState1
              (pointAddFiniteStart yst out left right)) = 0
        · have hhi := invNormBound_of_canonical _
            (hready.doubleDenCanonical hleft hright heq hy)
          have heq2 := hready.doubleEqStable hleft hright heq hy
          exact ⟨pointAddFiniteDoubleFinal
              (pointAddFiniteStart yst out left right), .normal,
            step_pointAddDouble yst out left right hleft hright heq hy
              hhi heq2,
            Or.inl rfl⟩
        · exact ⟨pointAddYZeroFinalState
              (pointAddDoubleState1
                (pointAddFiniteStart yst out left right)), .leave,
            step_pointAddYZero yst out left right hleft hright heq hy,
            Or.inr rfl⟩
    · exact ⟨pointAddRightFinalState yst out left right, .leave,
        step_pointAddRightIdentity yst out left right hleft hright,
        Or.inr rfl⟩
  · exact ⟨pointAddLeftFinalState yst out left right, .leave,
      step_pointAddLeftIdentity yst out left right hleft, Or.inr rfl⟩

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
