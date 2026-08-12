import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPostY

set_option warningAsError true

/-! # Lawful affine endpoint of the frozen G2ADD postlude -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def mainPostPoint (st : EvmState) : G2Affine.Point :=
  .affine (Fp2.toLawful (fp2At (mainPostState5 st) 2688))
    (Fp2.toLawful (fp2At (mainPostState5 st) 2944))

theorem mainPostCoordinates_canonical (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hy1 : Fp2.Canonical (fp2At st 128))
    (hx2 : Fp2.Canonical (fp2At st 256)) :
    Fp2.Canonical (fp2At (mainPostState5 st) 2688) ∧
      Fp2.Canonical (fp2At (mainPostState5 st) 2944) := by
  constructor
  · rw [mainPostState5_x3]
    exact mainPostState2_canonical st hlam hx1 hx2
  · exact mainPostState5_canonical st hlam hx1 hy1 hx2

theorem mainPostPoint_eq_add_of_x_ne (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hy1 : Fp2.Canonical (fp2At st 128))
    (hx2 : Fp2.Canonical (fp2At st 256))
    (hxne : Fp2.toLawful (fp2At st 0) ≠ Fp2.toLawful (fp2At st 256))
    (hslope : Fp2.toLawful (fp2At st 2048) =
      (Fp2.toLawful (fp2At st 384) - Fp2.toLawful (fp2At st 128)) /
        (Fp2.toLawful (fp2At st 256) - Fp2.toLawful (fp2At st 0))) :
    mainPostPoint st =
      G2Affine.add
        (.affine (Fp2.toLawful (fp2At st 0))
          (Fp2.toLawful (fp2At st 128)))
        (.affine (Fp2.toLawful (fp2At st 256))
          (Fp2.toLawful (fp2At st 384))) := by
  rw [G2Affine.add, LawfulAffine.add_of_x_ne _ _ _ _ _ hxne]
  simp only [mainPostPoint]
  rw [mainPostState5_toLawful st hlam hx1 hy1 hx2,
    mainPostState5_x3, mainPostState2_toLawful st hlam hx1 hx2, hslope]

theorem mainPostPoint_eq_double (st : EvmState)
    (hlam : Fp2.Canonical (fp2At st 2048))
    (hx1 : Fp2.Canonical (fp2At st 0))
    (hy1 : Fp2.Canonical (fp2At st 128))
    (hx2 : Fp2.Canonical (fp2At st 256))
    (hyne : Fp2.toLawful (fp2At st 128) ≠ 0)
    (hxEq : Fp2.toLawful (fp2At st 256) = Fp2.toLawful (fp2At st 0))
    (hslope : Fp2.toLawful (fp2At st 2048) =
      (3 * Fp2.toLawful (fp2At st 0) ^ 2) /
        (2 * Fp2.toLawful (fp2At st 128))) :
    mainPostPoint st =
      G2Affine.double
        (.affine (Fp2.toLawful (fp2At st 0))
          (Fp2.toLawful (fp2At st 128))) := by
  simp only [mainPostPoint, G2Affine.double, LawfulAffine.double,
    hyne, ↓reduceIte, G2Affine.curve]
  rw [mainPostState5_toLawful st hlam hx1 hy1 hx2,
    mainPostState5_x3, mainPostState2_toLawful st hlam hx1 hx2,
    hslope, hxEq]
  ring_nf

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
