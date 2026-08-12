import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvMemory

set_option warningAsError true

/-! # Recovered values for frozen G2ADD `fp2Inv`

Each theorem crosses one already-compiled source/memory boundary.  The module
does not unfold the complete inversion DAG; later semantic composition sees
only the input components, norm inverse, and real result.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2InvRealLeft_eq (yst : EvmState) (a : U256)
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    fp2InvRealLeft yst a = (fp2At yst a).c0 := by
  have h32 : (a + BitVec.ofNat 256 32).toNat = a.toNat + 32 := by
    bv_omega
  rw [fp2InvRealLeft,
    fp2InvAfterScalarStores_loadWord_high _ _ a.toNat (by omega),
    h32,
    fp2InvAfterScalarStores_loadWord_high _ _ (a.toNat + 32) (by omega)]
  change fpWords (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a.toNat + 32)) =
      fpWords (loadWord yst.memory a.toNat)
        (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
  rw [h32]

theorem fp2InvNorm_eq_input_squares (yst : EvmState) (a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    pairWords (fp2InvNorm yst a) =
      Fp.addSource
        (Fp.mulCanonical (fp2At yst a).c0 (fp2At yst a).c0)
        (Fp.mulCanonical (fp2At yst a).c1 (fp2At yst a).c1) := by
  have hinput : Fp.Canonical (fp2InvSquare1Input yst a) := by
    rw [fp2InvSquare1Input_eq yst a haHigh ha]
    exact haCanonical.c1.proof
  rw [fp2InvNorm_eq_squares,
    fp2InvSquare0_eq_mulCanonical yst a haCanonical.c0.proof,
    fp2InvSquare1_eq_mulCanonical yst a hinput,
    fp2InvSquare1Input_eq yst a haHigh ha]
  rfl

theorem fp2InvScalarStored_eq (yst : EvmState) (a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    fp2InvScalarStored yst a =
      Fp.invCanonical
        (Fp.addSource
          (Fp.mulCanonical (fp2At yst a).c0 (fp2At yst a).c0)
          (Fp.mulCanonical (fp2At yst a).c1 (fp2At yst a).c1)) := by
  have hs := fp2InvSquares_canonical yst a haCanonical haHigh ha
  rw [fp2InvAfterScalarStores_scalar,
    fp2InvScalar_eq_invCanonical yst a
      (fp2InvNorm_canonical yst a hs.1 hs.2),
    fp2InvNorm_eq_input_squares yst a haCanonical haHigh ha]

theorem fp2InvReal_eq (yst : EvmState) (a : U256)
    (haCanonical : Fp2.Canonical (fp2At yst a))
    (haHigh : 1920 ≤ a.toNat) (ha : a.toNat + 96 < 2 ^ 256) :
    pairWords (fp2InvReal yst a) =
      Fp.mulCanonical (fp2At yst a).c0
        (Fp.invCanonical
          (Fp.addSource
            (Fp.mulCanonical (fp2At yst a).c0 (fp2At yst a).c0)
            (Fp.mulCanonical (fp2At yst a).c1 (fp2At yst a).c1))) := by
  let norm := Fp.addSource
    (Fp.mulCanonical (fp2At yst a).c0 (fp2At yst a).c0)
    (Fp.mulCanonical (fp2At yst a).c1 (fp2At yst a).c1)
  have hnorm : Fp.Canonical norm := by
    exact Fp.canonical_addSource
      (Fp.canonical_mulCanonical haCanonical.c0.proof haCanonical.c0.proof)
      (Fp.canonical_mulCanonical haCanonical.c1.proof haCanonical.c1.proof)
  have hleft : Fp.Canonical (fp2InvRealLeft yst a) := by
    rw [fp2InvRealLeft_eq yst a haHigh ha]
    exact haCanonical.c0.proof
  have hscalar : Fp.Canonical (fp2InvScalarStored yst a) := by
    rw [fp2InvScalarStored_eq yst a haCanonical haHigh ha]
    exact Fp.canonical_invCanonical hnorm
  rw [fp2InvReal_eq_mulCanonical yst a hleft hscalar,
    fp2InvRealLeft_eq yst a haHigh ha,
    fp2InvScalarStored_eq yst a haCanonical haHigh ha]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
