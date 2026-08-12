import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDispatcher
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteLowMemory
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteExceptionalLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainDoubleLambda
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainUnequalLambda
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPostOutput

set_option warningAsError true

/-! # Complete lawful outputs of the frozen G2ADD finite dispatcher -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- The nonexceptional doubling path returns the lawful affine sum of the
equal finite input point with itself. -/
theorem mainFiniteDispatcher_double_returned_add (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256))
    (hyne : Fp2.toLawful (fp2At (mainValidatedState yst) 128) ≠ 0)
    (hxEq : Fp2.toLawful (fp2At (mainValidatedState yst) 256) =
      Fp2.toLawful (fp2At (mainValidatedState yst) 0)) :
    (mainPostReturnState (mainAfterDoubleXEq2 yst)).halted =
      some (HaltKind.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add
            (.affine (Fp2.toLawful (fp2At (mainValidatedState yst) 0))
              (Fp2.toLawful (fp2At (mainValidatedState yst) 128)))
            (.affine (Fp2.toLawful (fp2At (mainValidatedState yst) 0))
              (Fp2.toLawful (fp2At (mainValidatedState yst) 128)))))).toList) := by
  have hlam : Fp2.Canonical
      (fp2At (mainAfterDoubleXEq2 yst) 2048) := by
    rw [mainAfterDoubleXEq2_fp2At]
    exact mainDoubleFinalState_canonical yst hx1 hy1
  have hx1' : Fp2.Canonical
      (fp2At (mainAfterDoubleXEq2 yst) 0) := by
    rw [mainAfterDoubleXEq2_fp2At_low _ _ (by decide) (by decide)]
    exact hx1
  have hy1' : Fp2.Canonical
      (fp2At (mainAfterDoubleXEq2 yst) 128) := by
    rw [mainAfterDoubleXEq2_fp2At_low _ _ (by decide) (by decide)]
    exact hy1
  have hx2' : Fp2.Canonical
      (fp2At (mainAfterDoubleXEq2 yst) 256) := by
    rw [mainAfterDoubleXEq2_fp2At_low _ _ (by decide) (by decide)]
    exact hx2
  rw [mainPost_returned_codec (mainAfterDoubleXEq2 yst)
    hlam hx1' hy1' hx2']
  congr 2
  apply congrArg (fun point => (Codec.encodeG2 (G2Affine.toWire point)).toList)
  rw [mainPostPoint_eq_double (mainAfterDoubleXEq2 yst)
    hlam hx1' hy1' hx2']
  · have hpoint :
        (.affine
          (Fp2.toLawful (fp2At (mainAfterDoubleXEq2 yst) 0))
          (Fp2.toLawful (fp2At (mainAfterDoubleXEq2 yst) 128)) :
            G2Affine.Point) =
        .affine (Fp2.toLawful (fp2At (mainValidatedState yst) 0))
          (Fp2.toLawful (fp2At (mainValidatedState yst) 128)) := by
      rw [mainAfterDoubleXEq2_fp2At_low _ 0 (by decide) (by decide),
        mainAfterDoubleXEq2_fp2At_low _ 128 (by decide) (by decide)]
    rw [hpoint]
    have hsum : Fp2.toLawful (fp2At (mainValidatedState yst) 128) +
        Fp2.toLawful (fp2At (mainValidatedState yst) 128) ≠ 0 := by
      rw [← two_mul]
      exact mul_ne_zero G2Affine.two_ne_zero hyne
    exact (LawfulAffine.add_self_of_sum_ne_zero
      G2Affine.curve _ _ hsum).symm
  · rw [mainAfterDoubleXEq2_fp2At_low _ 128 (by decide) (by decide)]
    exact hyne
  · rw [mainAfterDoubleXEq2_fp2At_low _ 256 (by decide) (by decide),
      mainAfterDoubleXEq2_fp2At_low _ 0 (by decide) (by decide)]
    exact hxEq
  · rw [mainAfterDoubleXEq2_fp2At,
      mainDoubleFinalState_toLawful yst hx1 hy1]
    rw [mainAfterDoubleXEq2_fp2At_low _ 0 (by decide) (by decide),
      mainAfterDoubleXEq2_fp2At_low _ 128 (by decide) (by decide)]

/-- The unequal-x path returns the lawful affine sum of the two finite input
points. -/
theorem mainFiniteDispatcher_unequal_returned_add (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256))
    (hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384))
    (hxne : Fp2.toLawful (fp2At (mainValidatedState yst) 0) ≠
      Fp2.toLawful (fp2At (mainValidatedState yst) 256)) :
    (mainPostReturnState (mainUnequalFinalState yst)).halted =
      some (HaltKind.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add
            (.affine (Fp2.toLawful (fp2At (mainValidatedState yst) 0))
              (Fp2.toLawful (fp2At (mainValidatedState yst) 128)))
            (.affine (Fp2.toLawful (fp2At (mainValidatedState yst) 256))
              (Fp2.toLawful (fp2At (mainValidatedState yst) 384)))))).toList) := by
  have hlam : Fp2.Canonical (fp2At (mainUnequalFinalState yst) 2048) :=
    mainUnequalFinalState_canonical yst hx1 hy1 hx2 hy2
  have hx1' : Fp2.Canonical (fp2At (mainUnequalFinalState yst) 0) := by
    rw [mainUnequalFinalState_fp2At_low _ _ (by decide) (by decide)]
    exact hx1
  have hy1' : Fp2.Canonical (fp2At (mainUnequalFinalState yst) 128) := by
    rw [mainUnequalFinalState_fp2At_low _ _ (by decide) (by decide)]
    exact hy1
  have hx2' : Fp2.Canonical (fp2At (mainUnequalFinalState yst) 256) := by
    rw [mainUnequalFinalState_fp2At_low _ _ (by decide) (by decide)]
    exact hx2
  rw [mainPost_returned_codec (mainUnequalFinalState yst)
    hlam hx1' hy1' hx2']
  congr 2
  apply congrArg (fun point => (Codec.encodeG2 (G2Affine.toWire point)).toList)
  rw [mainPostPoint_eq_add_of_x_ne (mainUnequalFinalState yst)
    hlam hx1' hy1' hx2']
  · rw [mainUnequalFinalState_fp2At_low _ 0 (by decide) (by decide),
      mainUnequalFinalState_fp2At_low _ 128 (by decide) (by decide),
      mainUnequalFinalState_fp2At_low _ 256 (by decide) (by decide),
      mainUnequalFinalState_fp2At_low _ 384 (by decide) (by decide)]
  · rw [mainUnequalFinalState_fp2At_low _ 0 (by decide) (by decide),
      mainUnequalFinalState_fp2At_low _ 256 (by decide) (by decide)]
    exact hxne
  · rw [mainUnequalFinalState_toLawful yst hx1 hy1 hx2 hy2]
    rw [mainUnequalFinalState_fp2At_low _ 0 (by decide) (by decide),
      mainUnequalFinalState_fp2At_low _ 128 (by decide) (by decide),
      mainUnequalFinalState_fp2At_low _ 256 (by decide) (by decide),
      mainUnequalFinalState_fp2At_low _ 384 (by decide) (by decide)]

/-- Opposite equal-x points return the lawful sum, namely infinity. -/
theorem mainFiniteDispatcher_opposite_returned_add (yst : EvmState)
    (x y1 y2 : G2Affine.Field) (hopposite : y1 + y2 = 0) :
    (mainFiniteClearReturnState yst).halted =
      some (HaltKind.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (.affine x y1) (.affine x y2)))).toList) := by
  rw [mainFiniteClear_returned_codec,
    mainFiniteOpposite_affineInfinity x y1 y2 hopposite]
  rfl

/-- Equal points with zero y-coordinate return the lawful sum, namely
infinity. -/
theorem mainFiniteDispatcher_zeroY_returned_add (yst : EvmState)
    (x : G2Affine.Field) :
    (mainFiniteClearReturnState yst).halted =
      some (HaltKind.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (.affine x 0) (.affine x 0)))).toList) := by
  rw [mainFiniteClear_returned_codec]
  simp [G2Affine.toWire, G2Affine.add, LawfulAffine.add]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
