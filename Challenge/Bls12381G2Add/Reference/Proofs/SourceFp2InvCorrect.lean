import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvOutput

set_option warningAsError true

/-! # Lawful refinement of frozen G2ADD `fp2Inv`

The frozen helper uses ordinary multiplication for its two squares and
subtraction from zero for negation.  These named values preserve that exact
schedule while each proof composes only opaque lawful Fp endpoints.  No
whole-DAG definitional equality or pinned opaque Fp2 inversion is used.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem canonical_zeroWords : Fp.Canonical (fpWords 0 0) := by
  change Fp.Canonical (Fp.pack 0)
  exact Fp.canonical_pack (by norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU])

def fp2InvRecoveredNorm (a : Fp2.Repr) : Fp.Limbs :=
  Fp.addSource (Fp.mulCanonical a.c0 a.c0) (Fp.mulCanonical a.c1 a.c1)

def fp2InvRecoveredScalar (a : Fp2.Repr) : Fp.Limbs :=
  Fp.invCanonical (fp2InvRecoveredNorm a)

def fp2InvRecovered (a : Fp2.Repr) : Fp2.Repr :=
  Fp2.mkRepr
    (Fp.mulCanonical a.c0 (fp2InvRecoveredScalar a))
    (Fp.mulCanonical (Fp.subSource (fpWords 0 0) a.c1)
      (fp2InvRecoveredScalar a))

theorem fp2InvRecovered_eq (a : Fp2.Repr) :
    fp2InvRecovered a =
      Fp2.mkRepr
        (Fp.mulCanonical a.c0
          (Fp.invCanonical
            (Fp.addSource (Fp.mulCanonical a.c0 a.c0)
              (Fp.mulCanonical a.c1 a.c1))))
        (Fp.mulCanonical (Fp.subSource (fpWords 0 0) a.c1)
          (Fp.invCanonical
            (Fp.addSource (Fp.mulCanonical a.c0 a.c0)
              (Fp.mulCanonical a.c1 a.c1)))) := by
  rfl

private theorem evalLawful_mulCanonical {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    PrimeField.finEquiv (Fp.toField (Fp.mulCanonical a b)) =
      PrimeField.finEquiv (Fp.toField a) *
        PrimeField.finEquiv (Fp.toField b) := by
  rw [Fp.toField_mulCanonical ha hb, map_mul]

private theorem canonical_fp2InvRecoveredNorm {a : Fp2.Repr}
    (ha : Fp2.Canonical a) : Fp.Canonical (fp2InvRecoveredNorm a) := by
  exact Fp.canonical_addSource
    (Fp.canonical_mulCanonical ha.c0.proof ha.c0.proof)
    (Fp.canonical_mulCanonical ha.c1.proof ha.c1.proof)

private theorem evalLawful_fp2InvRecoveredNorm {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    PrimeField.finEquiv (Fp.toField (fp2InvRecoveredNorm a)) =
      (PrimeField.finEquiv (Fp.toField a.c0)) ^ 2 +
        (PrimeField.finEquiv (Fp.toField a.c1)) ^ 2 := by
  have hs0 := Fp.canonical_mulCanonical ha.c0.proof ha.c0.proof
  have hs1 := Fp.canonical_mulCanonical ha.c1.proof ha.c1.proof
  unfold fp2InvRecoveredNorm
  change PrimeField.finEquiv (Fp.toField
    (Fp.addSource (Fp.mulCanonical a.c0 a.c0)
      (Fp.mulCanonical a.c1 a.c1))) = _
  rw [Fp.toLawful_addSource hs0 hs1,
    evalLawful_mulCanonical ha.c0.proof ha.c0.proof,
    evalLawful_mulCanonical ha.c1.proof ha.c1.proof]
  simp only [pow_two]

private theorem canonical_fp2InvRecoveredScalar {a : Fp2.Repr}
    (ha : Fp2.Canonical a) : Fp.Canonical (fp2InvRecoveredScalar a) := by
  exact Fp.canonical_invCanonical (canonical_fp2InvRecoveredNorm ha)

private theorem evalLawful_fp2InvRecoveredScalar {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    PrimeField.finEquiv (Fp.toField (fp2InvRecoveredScalar a)) =
      ((PrimeField.finEquiv (Fp.toField a.c0)) ^ 2 +
        (PrimeField.finEquiv (Fp.toField a.c1)) ^ 2)⁻¹ := by
  unfold fp2InvRecoveredScalar
  rw [Fp.toLawful_invCanonical (canonical_fp2InvRecoveredNorm ha),
    evalLawful_fp2InvRecoveredNorm ha]

private theorem canonical_fp2InvRecoveredNeg {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    Fp.Canonical (Fp.subSource (fpWords 0 0) a.c1) :=
  Fp.canonical_subSource canonical_zeroWords ha.c1.proof

private theorem evalLawful_fp2InvRecoveredNeg {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    PrimeField.finEquiv
        (Fp.toField (Fp.subSource (fpWords 0 0) a.c1)) =
      -PrimeField.finEquiv (Fp.toField a.c1) := by
  rw [Fp.toLawful_subSource canonical_zeroWords ha.c1.proof]
  have hzero : PrimeField.finEquiv (Fp.toField (fpWords 0 0)) = 0 := by rfl
  rw [hzero, zero_sub]

theorem canonical_fp2InvRecovered {a : Fp2.Repr}
    (ha : Fp2.Canonical a) : Fp2.Canonical (fp2InvRecovered a) := by
  apply Fp2.canonical_mkRepr
  · exact ⟨Fp.canonical_mulCanonical ha.c0.proof
      (canonical_fp2InvRecoveredScalar ha)⟩
  · exact ⟨Fp.canonical_mulCanonical
      (canonical_fp2InvRecoveredNeg ha)
      (canonical_fp2InvRecoveredScalar ha)⟩

private theorem evalLawful_fp2InvRecovered_c0 {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    PrimeField.finEquiv (Fp.toField (fp2InvRecovered a).c0) =
      PrimeField.finEquiv (Fp.toField a.c0) *
        ((PrimeField.finEquiv (Fp.toField a.c0)) ^ 2 +
          (PrimeField.finEquiv (Fp.toField a.c1)) ^ 2)⁻¹ := by
  unfold fp2InvRecovered
  change PrimeField.finEquiv (Fp.toField
    (Fp.mulCanonical a.c0 (fp2InvRecoveredScalar a))) = _
  rw [evalLawful_mulCanonical ha.c0.proof
    (canonical_fp2InvRecoveredScalar ha),
    evalLawful_fp2InvRecoveredScalar ha]

private theorem evalLawful_fp2InvRecovered_c1 {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    PrimeField.finEquiv (Fp.toField (fp2InvRecovered a).c1) =
      (-PrimeField.finEquiv (Fp.toField a.c1)) *
        ((PrimeField.finEquiv (Fp.toField a.c0)) ^ 2 +
          (PrimeField.finEquiv (Fp.toField a.c1)) ^ 2)⁻¹ := by
  unfold fp2InvRecovered
  change PrimeField.finEquiv (Fp.toField
    (Fp.mulCanonical (Fp.subSource (fpWords 0 0) a.c1)
      (fp2InvRecoveredScalar a))) = _
  rw [evalLawful_mulCanonical (canonical_fp2InvRecoveredNeg ha)
    (canonical_fp2InvRecoveredScalar ha),
    evalLawful_fp2InvRecoveredNeg ha,
    evalLawful_fp2InvRecoveredScalar ha]

theorem toLawful_fp2InvRecovered {a : Fp2.Repr}
    (ha : Fp2.Canonical a) :
    Fp2.toLawful (fp2InvRecovered a) = (Fp2.toLawful a)⁻¹ := by
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.re_inv, QuadraticAlgebra.norm_def]
    simp only [zero_mul, add_zero, neg_mul, one_mul, sub_neg_eq_add]
    rw [show (Fp2.toLawful a).re =
        PrimeField.finEquiv (Fp.toField a.c0) by rfl,
      show (Fp2.toLawful a).im =
        PrimeField.finEquiv (Fp.toField a.c1) by rfl]
    change PrimeField.finEquiv
      (Fp.toField (fp2InvRecovered a).c0) = _
    rw [evalLawful_fp2InvRecovered_c0 ha]
    simp only [pow_two]
    rw [add_comm
      (PrimeField.finEquiv (Fp.toField a.c0) *
        PrimeField.finEquiv (Fp.toField a.c0))
      (PrimeField.finEquiv (Fp.toField a.c1) *
        PrimeField.finEquiv (Fp.toField a.c1))]
    rw [mul_comm]
  · rw [QuadraticAlgebra.im_inv, QuadraticAlgebra.norm_def]
    simp only [zero_mul, add_zero, neg_mul, one_mul, sub_neg_eq_add]
    rw [show (Fp2.toLawful a).re =
        PrimeField.finEquiv (Fp.toField a.c0) by rfl,
      show (Fp2.toLawful a).im =
        PrimeField.finEquiv (Fp.toField a.c1) by rfl]
    change PrimeField.finEquiv
      (Fp.toField (fp2InvRecovered a).c1) = _
    rw [evalLawful_fp2InvRecovered_c1 ha]
    simp only [pow_two]
    ring

theorem fp2InvFinalState_eq_recovered (yst : EvmState) (out a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256)
    (hdisjoint : a.toNat + 128 ≤ out.toNat)
    (houtHigh : 1728 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2InvFinalState yst out a) out =
      fp2InvRecovered (fp2At yst a) := by
  rw [fp2InvFinalState_output yst out a (by omega) hout,
    fp2InvReal_eq yst a haCanonical haHigh ha,
    fp2InvImag_eq yst out a haCanonical haHigh ha hdisjoint houtHigh
      (by omega),
    fp2InvRecovered_eq]

theorem fp2InvFinalState_toLawful (yst : EvmState) (out a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256)
    (hdisjoint : a.toNat + 128 ≤ out.toNat)
    (houtHigh : 1728 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2InvFinalState yst out a) out) =
      (Fp2.toLawful (fp2At yst a))⁻¹ := by
  rw [fp2InvFinalState_eq_recovered yst out a haCanonical haHigh ha
    hdisjoint houtHigh hout]
  exact toLawful_fp2InvRecovered haCanonical

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
