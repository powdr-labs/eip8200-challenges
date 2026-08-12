import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDispatcher

set_option warningAsError true

/-! # Complete G1ADD finite-dispatch lawful outputs -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev LawfulFp := PrimeField.LawfulFp

private def toLawful (a : Fp.Limbs) : LawfulFp :=
  PrimeField.finEquiv (Fp.toField a)

/-- The specification-facing encoded result of the unequal-x affine branch.
This value is small enough for contract consumers to name without exposing the
constructed execution state that produced it. -/
def mainFiniteUnequalExpected (yst : EvmState) : List UInt8 :=
  (Codec.encodeG1 (G1Affine.toWire
    (G1Affine.add
      (.affine (PrimeField.finEquiv (Fp.toField (mainFinitePostX1 yst)))
        (PrimeField.finEquiv (Fp.toField (mainFinitePostY1 yst))))
      (.affine (PrimeField.finEquiv (Fp.toField (mainFinitePostX2 yst)))
        (PrimeField.finEquiv
          (Fp.toField (mainFiniteUnequalY2 yst))))))).toList

/-- The frozen unequal-x test implies distinct lawful x coordinates for
canonical inputs. -/
theorem mainFiniteXEq_zero_lawful (yst : EvmState)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hxeq : mainFiniteXEqValue yst = 0) :
    PrimeField.finEquiv (Fp.toField (mainFinitePostX1 yst)) ≠
      PrimeField.finEquiv (Fp.toField (mainFinitePostX2 yst)) := by
  change toLawful (mainFinitePostX1 yst) ≠
    toLawful (mainFinitePostX2 yst)
  intro heq
  have hvalue := Fp.value_eq_of_lawful_eq hx1 hx2 heq
  have hlimbs := Fp.limbs_ext_of_value_eq hvalue
  have hone : mainFiniteXEqValue yst = 1 := by
    apply (mainFiniteXEq_eq_one_iff yst).mpr
    constructor
    · apply YulEvmCompiler.conv_injective
      exact congrArg Fp.Limbs.hi hlimbs
    · apply YulEvmCompiler.conv_injective
      exact congrArg Fp.Limbs.lo hlimbs
  exact (by decide : (0 : U256) ≠ 1) (hxeq.symm.trans hone)

/-- The complete nonexceptional doubling branch returns the lawful affine
sum of its equal finite input point with itself. -/
theorem mainFiniteDispatcher_double_returned_add (yst : EvmState)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical
      (mainFinitePostLambda (mainFiniteDoubleLambdaWords yst)))
    (hyne : toLawful (mainFinitePostY1 yst) ≠ 0)
    (hxEq : toLawful (mainFinitePostX2 yst) =
      toLawful (mainFinitePostX1 yst))
    (hslope : toLawful
        (mainFinitePostLambda (mainFiniteDoubleLambdaWords yst)) =
      (3 * toLawful (mainFinitePostX1 yst) ^ 2) /
        (2 * toLawful (mainFinitePostY1 yst))) :
    (mainFinitePostReturnState yst (mainFiniteDoublePostState yst)
      (mainFiniteDoubleLambdaWords yst)).halted =
      some (HaltKind.ret,
        (Codec.encodeG1 (G1Affine.toWire
          (G1Affine.add
            (.affine (toLawful (mainFinitePostX1 yst))
              (toLawful (mainFinitePostY1 yst)))
            (.affine (toLawful (mainFinitePostX1 yst))
              (toLawful (mainFinitePostY1 yst)))))).toList) := by
  rw [mainFinitePost_returned_codec yst (mainFiniteDoublePostState yst)
    (mainFiniteDoubleLambdaWords yst) hx1 hy1 hx2 hlam]
  congr 2
  apply congrArg (fun point =>
    (Codec.encodeG1 (G1Affine.toWire point)).toList)
  rw [mainFinitePostPoint_eq_double yst (mainFiniteDoublePostState yst)
    (mainFiniteDoubleLambdaWords yst) hx1 hy1 hx2 hlam hyne hxEq hslope]
  have hsum : toLawful (mainFinitePostY1 yst) +
      toLawful (mainFinitePostY1 yst) ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero G1Affine.two_ne_zero hyne
  exact (LawfulAffine.add_self_of_sum_ne_zero G1Affine.curve _ _ hsum).symm

/-- The complete unequal-x branch returns the lawful affine sum. -/
theorem mainFiniteDispatcher_unequal_returned_add (yst : EvmState)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical
      (mainFinitePostLambda (mainFiniteUnequalLambdaWords yst)))
    (hxne : toLawful (mainFinitePostX1 yst) ≠
      toLawful (mainFinitePostX2 yst))
    (hslope : toLawful
        (mainFinitePostLambda (mainFiniteUnequalLambdaWords yst)) =
      (toLawful (mainFiniteUnequalY2 yst) -
        toLawful (mainFinitePostY1 yst)) /
      (toLawful (mainFinitePostX2 yst) -
        toLawful (mainFinitePostX1 yst))) :
    (mainFinitePostReturnState yst (mainFiniteUnequalFinalState yst)
      (mainFiniteUnequalLambdaWords yst)).halted =
      some (HaltKind.ret,
        (Codec.encodeG1 (G1Affine.toWire
          (G1Affine.add
            (.affine (toLawful (mainFinitePostX1 yst))
              (toLawful (mainFinitePostY1 yst)))
            (.affine (toLawful (mainFinitePostX2 yst))
              (toLawful (mainFiniteUnequalY2 yst)))))).toList) := by
  rw [mainFinitePost_returned_codec yst (mainFiniteUnequalFinalState yst)
    (mainFiniteUnequalLambdaWords yst) hx1 hy1 hx2 hlam]
  congr 2
  apply congrArg (fun point =>
    (Codec.encodeG1 (G1Affine.toWire point)).toList)
  exact mainFinitePostPoint_eq_add_of_x_ne yst
    (mainFiniteUnequalFinalState yst) (mainFiniteUnequalLambdaWords yst)
    hx1 hy1 hx2 hlam hxne hslope

/-- Compact characterization of the unequal-x return value. -/
theorem mainFiniteDispatcher_unequal_returned_expected (yst : EvmState)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical
      (mainFinitePostLambda (mainFiniteUnequalLambdaWords yst)))
    (hxne : toLawful (mainFinitePostX1 yst) ≠
      toLawful (mainFinitePostX2 yst))
    (hslope : toLawful
        (mainFinitePostLambda (mainFiniteUnequalLambdaWords yst)) =
      (toLawful (mainFiniteUnequalY2 yst) -
        toLawful (mainFinitePostY1 yst)) /
      (toLawful (mainFinitePostX2 yst) -
        toLawful (mainFinitePostX1 yst))) :
    (mainFinitePostReturnState yst (mainFiniteUnequalFinalState yst)
      (mainFiniteUnequalLambdaWords yst)).halted =
      some (HaltKind.ret, mainFiniteUnequalExpected yst) := by
  simpa only [mainFiniteUnequalExpected, toLawful] using
    mainFiniteDispatcher_unequal_returned_add yst hx1 hy1 hx2 hlam hxne hslope

/-- Derive the compact unequal-x return characterization from canonical input
coordinates and the branch test. Lambda canonicality and slope correctness are
kept behind this boundary. -/
theorem mainFiniteDispatcher_unequal_returned_expected_of_inputs
    (yst : EvmState)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hy2 : Fp.Canonical (mainFiniteUnequalY2 yst))
    (hxeq : mainFiniteXEqValue yst = 0) :
    (mainFinitePostReturnState yst (mainFiniteUnequalFinalState yst)
      (mainFiniteUnequalLambdaWords yst)).halted =
      some (HaltKind.ret, mainFiniteUnequalExpected yst) := by
  have hlam := canonical_mainFiniteUnequalLambda yst hx1 hy1 hx2 hy2
  have hxne := mainFiniteXEq_zero_lawful yst hx1 hx2 hxeq
  have hslope := mainFiniteUnequalLambda_toLawful yst hx1 hy1 hx2 hy2 hxne
  apply mainFiniteDispatcher_unequal_returned_expected yst hx1 hy1 hx2
  · change Fp.Canonical (mainFiniteUnequalLambda yst)
    exact hlam
  · exact hxne
  · change PrimeField.finEquiv (Fp.toField (mainFiniteUnequalLambda yst)) =
      (PrimeField.finEquiv (Fp.toField (mainFiniteUnequalY2 yst)) -
        PrimeField.finEquiv (Fp.toField (mainFiniteUnequalY1 yst))) /
      (PrimeField.finEquiv (Fp.toField (mainFiniteUnequalX2 yst)) -
        PrimeField.finEquiv (Fp.toField (mainFiniteUnequalX1 yst)))
    exact hslope

/-- The opposite-point exceptional branch returns the lawful affine sum,
namely infinity. -/
theorem mainFiniteDispatcher_opposite_returned_add (yst : EvmState)
    (x y1 y2 : G1Affine.Field) (hopposite : y1 + y2 = 0) :
    (mainFiniteOppositeReturnState yst).halted =
      some (HaltKind.ret,
        (Codec.encodeG1 (G1Affine.toWire
          (G1Affine.add (.affine x y1) (.affine x y2)))).toList) := by
  rw [mainFiniteOpposite_returned_codec,
    mainFiniteOpposite_affineInfinity x y1 y2 hopposite]
  rfl

/-- The equal-point `y=0` exceptional branch returns the lawful affine sum,
namely infinity. -/
theorem mainFiniteDispatcher_zeroY_returned_add (yst : EvmState)
    (x : G1Affine.Field) :
    (mainFiniteZeroYReturnState yst).halted =
      some (HaltKind.ret,
        (Codec.encodeG1 (G1Affine.toWire
          (G1Affine.add (.affine x 0) (.affine x 0)))).toList) := by
  rw [mainFiniteZeroY_returned_codec]
  simp [G1Affine.toWire, G1Affine.add, LawfulAffine.add]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
