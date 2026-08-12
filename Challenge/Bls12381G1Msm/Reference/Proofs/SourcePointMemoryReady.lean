import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointMemoryPointers

set_option warningAsError true

/-! Canonical point-region invariant and the total `pointAdd` readiness adapter. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- One canonical affine-or-infinity point in the concrete high-memory area.
The four address facts express disjointness from all field/pointer scratch. -/
structure PointMemoryRegion (yst : EvmState) (ptr : U256) : Prop where
  xHiAboveScratch : 1632 ≤ ptr.toNat
  xLoAboveScratch : 1632 ≤ (ptr + 32).toNat
  yHiAboveScratch : 1632 ≤ (ptr + 64).toNat
  yLoAboveScratch : 1632 ≤ (ptr + 96).toNat
  canonicalX : Fp.Canonical (pointMemoryX yst ptr)
  canonicalY : Fp.Canonical (pointMemoryY yst ptr)

/-- The two input regions plus the fixed active-memory high-water boundary. -/
structure PointAddMemoryInvariant (yst : EvmState)
    (out left right : U256) : Prop where
  layout : PointAddFixedLayout yst out left right
  leftRegion : PointMemoryRegion yst left
  rightRegion : PointMemoryRegion yst right

private theorem canonical_toField_eq_zero_words {a : Fp.Limbs}
    (ha : Fp.Canonical a) (hzero : Fp.toField a = 0) :
    a.hi = 0 ∧ a.lo = 0 := by
  have hvalue := congrArg Fin.val hzero
  have hvalueZero : Fp.value a = 0 := by
    have hmod : Fp.value a % EvmSemantics.Crypto.Bls12381.p = 0 := by
      simpa [Fp.toField] using hvalue
    simpa [Nat.mod_eq_of_lt ha.2] using hmod
  have hhiNat : a.hi.toNat = 0 := by
    unfold Fp.value at hvalueZero
    have hmul : Challenge.EvmProof.Limbs.radix * a.hi.toNat = 0 :=
      Nat.eq_zero_of_add_eq_zero_left hvalueZero
    rcases Nat.mul_eq_zero.mp hmul with hradix | hhi
    · exact False.elim
        (Nat.ne_of_gt Challenge.EvmProof.Limbs.radix_pos hradix)
    · exact hhi
  have hloNat : a.lo.toNat = 0 := by
    unfold Fp.value at hvalueZero
    exact Nat.eq_zero_of_add_eq_zero_right hvalueZero
  exact ⟨Challenge.EvmProof.Word.word_ext (by
      calc
        a.hi.toNat = 0 := hhiNat
        _ = (0 : EvmSemantics.UInt256).toNat := rfl),
    Challenge.EvmProof.Word.word_ext (by
      calc
        a.lo.toNat = 0 := hloNat
        _ = (0 : EvmSemantics.UInt256).toNat := rfl)⟩

private theorem pointAddYSum_ne_zero_of_test (yst : EvmState)
    (out left right : U256)
    (hleft : Fp.Canonical (pointAddFiniteLeftYLimbs yst out left right))
    (hright : Fp.Canonical (pointAddFiniteRightYLimbs yst out left right))
    (hzero : pointAddYZeroValue yst out left right = 0) :
    Fp.toField (pointAddFiniteLeftYLimbs yst out left right) +
      Fp.toField (pointAddFiniteRightYLimbs yst out left right) ≠ 0 := by
  intro hsum
  have hsourceCanonical := Fp.canonical_addSource hleft hright
  have hsourceZero : Fp.toField
      (Fp.addSource (pointAddFiniteLeftYLimbs yst out left right)
        (pointAddFiniteRightYLimbs yst out left right)) = 0 := by
    rw [Fp.toField_addSource hleft hright]
    exact hsum
  have hwordsZero := canonical_toField_eq_zero_words hsourceCanonical hsourceZero
  have hresultZero : pointAddYSumResult yst out left right = (0, 0) := by
    have hrepr := pointAddYSumResult_toSource yst out left right
    have hconvZero : YulEvmCompiler.conv (0 : U256) =
        (0 : EvmSemantics.UInt256) := by
      apply YulEvmCompiler.u256ext
      rfl
    have hhi : (pointAddYSumResult yst out left right).1 = 0 := by
      have hconv : YulEvmCompiler.conv
          (pointAddYSumResult yst out left right).1 = 0 :=
        (congrArg Fp.Limbs.hi hrepr).trans hwordsZero.1
      apply YulEvmCompiler.conv_injective
      exact hconv.trans hconvZero.symm
    have hlo : (pointAddYSumResult yst out left right).2 = 0 := by
      have hconv : YulEvmCompiler.conv
          (pointAddYSumResult yst out left right).2 = 0 :=
        (congrArg Fp.Limbs.lo hrepr).trans hwordsZero.2
      apply YulEvmCompiler.conv_injective
      exact hconv.trans hconvZero.symm
    exact Prod.ext hhi hlo
  have hnonzero := (pointAddYZeroValue_eq_zero_iff yst out left right).mp hzero
  simp [pointAddYSumHi, pointAddYSumLo, hresultZero] at hnonzero

/-- Fixed, canonical point regions supply every lawful side condition needed
by the branchwise execution theorem. -/
theorem PointAddMemoryInvariant.pointAddReady {yst : EvmState}
    {out left right : U256}
    (h : PointAddMemoryInvariant yst out left right) :
    PointAddReady yst out left right := by
  constructor
  · intro _ _ _
    rw [pointAddUnequalLeftXLimbs_eq yst out left right
      h.leftRegion.xHiAboveScratch h.leftRegion.xLoAboveScratch]
    exact h.leftRegion.canonicalX
  · intro _ _ _
    rw [pointAddUnequalRightXLimbs_eq yst out left right
      h.rightRegion.xHiAboveScratch h.rightRegion.xLoAboveScratch]
    exact h.rightRegion.canonicalX
  · intro _ _ _
    exact pointAddUnequalInputsState_eq_of_fixed_layout yst out left right
      h.layout
  · intro _ _ _ _
    rw [pointAddFiniteLeftYLimbs_eq yst out left right
      h.leftRegion.yHiAboveScratch h.leftRegion.yLoAboveScratch]
    exact h.leftRegion.canonicalY
  · intro _ _ _ _
    rw [pointAddFiniteRightYLimbs_eq yst out left right
      h.rightRegion.yHiAboveScratch h.rightRegion.yLoAboveScratch]
    exact h.rightRegion.canonicalY
  · intro _ _ _ _
    rw [pointAddDoubleLeftYLimbs_eq yst out left right
      h.leftRegion.yHiAboveScratch h.leftRegion.yLoAboveScratch]
    exact h.leftRegion.canonicalY
  · intro _ _ _ hzero
    apply pointAddYSum_ne_zero_of_test yst out left right
    · rw [pointAddFiniteLeftYLimbs_eq yst out left right
        h.leftRegion.yHiAboveScratch h.leftRegion.yLoAboveScratch]
      exact h.leftRegion.canonicalY
    · rw [pointAddFiniteRightYLimbs_eq yst out left right
        h.rightRegion.yHiAboveScratch h.rightRegion.yLoAboveScratch]
      exact h.rightRegion.canonicalY
    · exact hzero

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
