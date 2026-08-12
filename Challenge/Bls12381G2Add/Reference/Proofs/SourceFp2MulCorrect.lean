import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulMemory

set_option warningAsError true

/-! # Functional refinement of frozen G2ADD `fp2Mul`

The execution and memory modules have already hidden the concrete MODEXP
states.  This final layer sees only the scheduled Fp2 inputs and the opaque
arithmetic phase equations.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def fp2MulLeftInput (yst : EvmState) (a b : U256) : Fp2.Repr :=
  Fp2.mkRepr (fp2MulV0Left yst a) (fp2MulV1Left yst a b)

def fp2MulRightInput (yst : EvmState) (a b : U256) : Fp2.Repr :=
  Fp2.mkRepr (fp2MulV0Right yst b) (fp2MulV1Right yst a b)

theorem fp2Mul_source_components (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2MulLeftInput yst a b))
    (hb : Fp2.Canonical (fp2MulRightInput yst a b))
    (hleft : fp2At (fp2MulAfterRealStores yst out a b) a =
      fp2MulLeftInput yst a b)
    (hright : fp2At (fp2MulAfterSumAStores yst out a b) b =
      fp2MulRightInput yst a b)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    pairWords (fp2MulReal yst a b) =
        Fp2.mulRealSource
          (Fp2.mulV0Source (fp2MulLeftInput yst a b)
            (fp2MulRightInput yst a b))
          (Fp2.mulV1Source (fp2MulLeftInput yst a b)
            (fp2MulRightInput yst a b)) ∧
      pairWords (fp2MulImag yst out a b) =
        Fp2.mulImaginarySource (fp2MulLeftInput yst a b)
          (fp2MulRightInput yst a b)
          (Fp2.mulV0Source (fp2MulLeftInput yst a b)
            (fp2MulRightInput yst a b))
          (Fp2.mulV1Source (fp2MulLeftInput yst a b)
            (fp2MulRightInput yst a b)) := by
  have hv0 : pairWords (fp2MulV0 yst a b) =
      Fp2.mulV0Source (fp2MulLeftInput yst a b)
        (fp2MulRightInput yst a b) := by
    exact fp2MulV0_eq_mulCanonical yst a b ha.c0.proof hb.c0.proof
  have hv1 : pairWords (fp2MulV1 yst a b) =
      Fp2.mulV1Source (fp2MulLeftInput yst a b)
        (fp2MulRightInput yst a b) := by
    exact fp2MulV1_eq_mulCanonical yst a b ha.c1.proof hb.c1.proof
  have hreal : pairWords (fp2MulReal yst a b) =
      Fp2.mulRealSource
        (Fp2.mulV0Source (fp2MulLeftInput yst a b)
          (fp2MulRightInput yst a b))
        (Fp2.mulV1Source (fp2MulLeftInput yst a b)
          (fp2MulRightInput yst a b)) := by
    rw [fp2MulReal_eq_products, hv0, hv1]
    rfl
  have hsumA : pairWords (fp2MulSumA yst out a b) =
      Fp.addSource (fp2MulLeftInput yst a b).c0
        (fp2MulLeftInput yst a b).c1 := by
    rw [fp2MulSumA_eq_addSource, hleft]
  have hsumB : pairWords (fp2MulSumB yst out a b) =
      Fp.addSource (fp2MulRightInput yst a b).c0
        (fp2MulRightInput yst a b).c1 := by
    rw [fp2MulSumB_eq_addSource, hright]
  have hsumACanonical : Fp.Canonical (pairWords (fp2MulSumA yst out a b)) := by
    rw [hsumA]
    exact Fp.canonical_addSource ha.c0.proof ha.c1.proof
  have hsumBCanonical : Fp.Canonical (pairWords (fp2MulSumB yst out a b)) := by
    rw [hsumB]
    exact Fp.canonical_addSource hb.c0.proof hb.c1.proof
  have hcross : pairWords (fp2MulCross yst out a b) =
      Fp.mulCanonical
        (Fp.addSource (fp2MulLeftInput yst a b).c0
          (fp2MulLeftInput yst a b).c1)
        (Fp.addSource (fp2MulRightInput yst a b).c0
          (fp2MulRightInput yst a b).c1) := by
    rw [fp2MulCross_eq_sums yst out a b hsumACanonical hsumBCanonical,
      hsumA, hsumB]
  have hproducts := fp2MulAfterCrossStores_products yst out a b houtHigh
    (by omega)
  have hvsum : pairWords (fp2MulVSum yst out a b) =
      Fp.addSource
        (Fp2.mulV0Source (fp2MulLeftInput yst a b)
          (fp2MulRightInput yst a b))
        (Fp2.mulV1Source (fp2MulLeftInput yst a b)
          (fp2MulRightInput yst a b)) := by
    rw [fp2MulVSum_eq_addSource, hproducts.1, hproducts.2, hv0, hv1]
  have himag : pairWords (fp2MulImag yst out a b) =
      Fp2.mulImaginarySource (fp2MulLeftInput yst a b)
        (fp2MulRightInput yst a b)
        (Fp2.mulV0Source (fp2MulLeftInput yst a b)
          (fp2MulRightInput yst a b))
        (Fp2.mulV1Source (fp2MulLeftInput yst a b)
          (fp2MulRightInput yst a b)) := by
    rw [fp2MulImag_eq_cross_vsum, hcross, hvsum]
    rfl
  exact ⟨hreal, himag⟩

theorem fp2MulFinalState_canonical (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2MulLeftInput yst a b))
    (hb : Fp2.Canonical (fp2MulRightInput yst a b))
    (hleft : fp2At (fp2MulAfterRealStores yst out a b) a =
      fp2MulLeftInput yst a b)
    (hright : fp2At (fp2MulAfterSumAStores yst out a b) b =
      fp2MulRightInput yst a b)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2MulFinalState yst out a b) out) := by
  have hc := fp2Mul_source_components yst out a b ha hb hleft hright
    houtHigh hout
  rw [Fp2.canonical_iff]
  constructor
  · rw [fp2MulFinalState_c0 yst out a b houtHigh hout, hc.1]
    exact (Fp2.canonical_mulC0Source ha hb).proof
  · rw [fp2MulFinalState_c1 yst out a b hout, hc.2]
    exact (Fp2.canonical_mulC1Source ha hb).proof

theorem fp2MulFinalState_toField_mul (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2MulLeftInput yst a b))
    (hb : Fp2.Canonical (fp2MulRightInput yst a b))
    (hleft : fp2At (fp2MulAfterRealStores yst out a b) a =
      fp2MulLeftInput yst a b)
    (hright : fp2At (fp2MulAfterSumAStores yst out a b) b =
      fp2MulRightInput yst a b)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.toField (fp2At (fp2MulFinalState yst out a b) out) =
      Fp2.toField (fp2MulLeftInput yst a b) *
        Fp2.toField (fp2MulRightInput yst a b) := by
  have hc := fp2Mul_source_components yst out a b ha hb hleft hright
    houtHigh hout
  unfold Fp2.toField
  rw [fp2MulFinalState_c0 yst out a b houtHigh hout,
    fp2MulFinalState_c1 yst out a b hout, hc.1, hc.2,
    Fp2.toField_mulC0Source ha hb, Fp2.toField_mulC1Source ha hb]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
