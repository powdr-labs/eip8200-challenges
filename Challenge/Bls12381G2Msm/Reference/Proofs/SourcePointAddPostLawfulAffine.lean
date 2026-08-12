import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPostLawfulStore

set_option warningAsError true

/-! Pure lawful affine meaning of the G2MSM point-add postlude formulas. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddPostPoint (st : EvmState) (left right leftY : U256) :
    G2Affine.Point :=
  .affine
    (Fp2.toLawful (fp2At st 2048) ^ 2 -
      Fp2.toLawful (fp2At st left) - Fp2.toLawful (fp2At st right))
    (Fp2.toLawful (fp2At st 2048) *
        (Fp2.toLawful (fp2At st left) -
          (Fp2.toLawful (fp2At st 2048) ^ 2 -
            Fp2.toLawful (fp2At st left) - Fp2.toLawful (fp2At st right))) -
      Fp2.toLawful (fp2At st leftY))

theorem pointAddPostPoint_eq_add_of_x_ne (st : EvmState)
    (left right leftY rightY : U256)
    (hxne : Fp2.toLawful (fp2At st left) ≠
      Fp2.toLawful (fp2At st right))
    (hslope : Fp2.toLawful (fp2At st 2048) =
      (Fp2.toLawful (fp2At st rightY) -
          Fp2.toLawful (fp2At st leftY)) /
        (Fp2.toLawful (fp2At st right) -
          Fp2.toLawful (fp2At st left))) :
    pointAddPostPoint st left right leftY =
      G2Affine.add
        (.affine (Fp2.toLawful (fp2At st left))
          (Fp2.toLawful (fp2At st leftY)))
        (.affine (Fp2.toLawful (fp2At st right))
          (Fp2.toLawful (fp2At st rightY))) := by
  rw [G2Affine.add, LawfulAffine.add_of_x_ne _ _ _ _ _ hxne]
  simp only [pointAddPostPoint]
  rw [hslope]

theorem pointAddPostPoint_eq_double (st : EvmState)
    (left leftY : U256)
    (hyne : Fp2.toLawful (fp2At st leftY) ≠ 0)
    (hslope : Fp2.toLawful (fp2At st 2048) =
      (3 * Fp2.toLawful (fp2At st left) ^ 2) /
        (2 * Fp2.toLawful (fp2At st leftY))) :
    pointAddPostPoint st left left leftY =
      G2Affine.double
        (.affine (Fp2.toLawful (fp2At st left))
          (Fp2.toLawful (fp2At st leftY))) := by
  simp only [pointAddPostPoint, G2Affine.double, LawfulAffine.double,
    hyne, ↓reduceIte, G2Affine.curve]
  rw [hslope]
  ring_nf

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
