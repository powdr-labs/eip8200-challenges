import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulCorrect

set_option warningAsError true

/-! # Lawful endpoint for frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2MulFinalState_toLawful_mul (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2MulLeftInput yst a b))
    (hb : Fp2.Canonical (fp2MulRightInput yst a b))
    (hleft : fp2At (fp2MulAfterRealStores yst out a b) a =
      fp2MulLeftInput yst a b)
    (hright : fp2At (fp2MulAfterSumAStores yst out a b) b =
      fp2MulRightInput yst a b)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2MulFinalState yst out a b) out) =
      Fp2.toLawful (fp2MulLeftInput yst a b) *
        Fp2.toLawful (fp2MulRightInput yst a b) := by
  unfold Fp2.toLawful
  rw [fp2MulFinalState_toField_mul yst out a b ha hb hleft hright
    houtHigh hout]
  exact LawfulFp2.ofWire_mul _ _

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
