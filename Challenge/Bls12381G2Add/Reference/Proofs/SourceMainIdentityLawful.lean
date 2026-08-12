import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDispatcherLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpecDecode
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFirstInfinity
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainSecondInfinity
import Challenge.Bls12381G2Add.Reference.Proofs.SourceCopyPointY

set_option warningAsError true

/-! # Lawful outputs of the frozen G2ADD identity branches -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev WirePoint := EvmSemantics.Crypto.Bls12381.G2Point

theorem mainValidatedState_fp2At_source (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainValidatedState yst) ptr = fp2At (mainDecodedState yst) ptr := by
  apply fp2At_eq_of_loads
  all_goals
    rw [mainValidatedState_loadWord_low yst _ (by bv_omega)]
    rfl

private theorem mainFirstInfinityCopyState_fp2At_x (yst : EvmState) :
    fp2At (mainFirstInfinityCopyState yst) 0 =
      fp2At (mainValidatedState yst) 256 := by
  exact copyPointState_256_fp2At_x _

private theorem mainFirstInfinityCopyState_fp2At_y (yst : EvmState) :
    fp2At (mainFirstInfinityCopyState yst) 128 =
      fp2At (mainValidatedState yst) 384 := by
  exact copyPointState_256_fp2At_y _

private theorem mainFirstInfinity_returned_other (yst : EvmState)
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256))
    (hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384)) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret, (Codec.encodeG2 (.affine
        (Fp2.toField (fp2At (mainValidatedState yst) 256))
        (Fp2.toField (fp2At (mainValidatedState yst) 384)))).toList) := by
  change some (HaltKind.ret,
    readBytes (mainFirstInfinityCopyState yst).memory 0 256) = _
  have hxCopy : Fp2.Canonical
      (fp2At (mainFirstInfinityCopyState yst) 0) := by
    rw [mainFirstInfinityCopyState_fp2At_x]
    exact hx2
  have hyCopy : Fp2.Canonical
      (fp2At (mainFirstInfinityCopyState yst) 128) := by
    rw [mainFirstInfinityCopyState_fp2At_y]
    exact hy2
  rw [readBytes_point_eq_encodeG2 _ hxCopy hyCopy,
    mainFirstInfinityCopyState_fp2At_x,
    mainFirstInfinityCopyState_fp2At_y]

private theorem mainSecondInfinity_returned_other (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret, (Codec.encodeG2 (.affine
        (Fp2.toField (fp2At (mainValidatedState yst) 0))
        (Fp2.toField (fp2At (mainValidatedState yst) 128)))).toList) := by
  change some (HaltKind.ret,
    readBytes (mainValidatedState yst).memory 0 256) = _
  rw [readBytes_point_eq_encodeG2 _ hx1 hy1]

theorem mainBothInfinity_returned_add (yst : EvmState)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst ≠ 0) :
    (mainBothInfinityReturnState yst).halted =
      some (HaltKind.ret, (Codec.encodeG2 (G2Affine.toWire
        (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
          (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  have hf : mainInf1 yst = 1 :=
    (mainInf1_zero_or_one yst).resolve_left hfirst
  have hs : mainInf2 yst = 1 :=
    (mainInf2_zero_or_one yst).resolve_left hsecond
  change (mainFiniteClearReturnState (mainValidatedState yst)).halted = _
  rw [mainFiniteClear_returned_codec]
  simp [sourcePoint1, sourcePoint2, hf, hs, G2Affine.ofWire,
    G2Affine.toWire, G2Affine.add]

theorem mainFirstInfinity_returned_add (yst : EvmState)
    (hvalid : mainValidationValue yst ≠ 0)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret, (Codec.encodeG2 (G2Affine.toWire
        (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
          (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  obtain ⟨_, hx2d, hy2d, _⟩ := mainValidation_canonical yst hvalid
  have hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256) := by
    rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hx2d
  have hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384) := by
    rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hy2d
  rw [mainFirstInfinity_returned_other yst hx2 hy2]
  rw [mainValidatedState_fp2At_source _ 256 (by decide) (by decide),
    mainValidatedState_fp2At_source _ 384 (by decide) (by decide)]
  have hf : mainInf1 yst = 1 :=
    (mainInf1_zero_or_one yst).resolve_left hfirst
  congr 2
  simp [sourcePoint1, sourcePoint2, hf, hsecond, G2Affine.ofWire,
    G2Affine.toWire, G2Affine.add, sourceFp2]

theorem mainSecondInfinity_returned_add (yst : EvmState)
    (hvalid : mainValidationValue yst ≠ 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst ≠ 0) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret, (Codec.encodeG2 (G2Affine.toWire
        (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
          (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  obtain ⟨⟨hx1d, hy1d, _⟩, _⟩ := mainValidation_canonical yst hvalid
  have hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0) := by
    rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hx1d
  have hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128) := by
    rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hy1d
  rw [mainSecondInfinity_returned_other yst hx1 hy1]
  rw [mainValidatedState_fp2At_source _ 0 (by decide) (by decide),
    mainValidatedState_fp2At_source _ 128 (by decide) (by decide)]
  have hs : mainInf2 yst = 1 :=
    (mainInf2_zero_or_one yst).resolve_left hsecond
  congr 2
  simp [sourcePoint1, sourcePoint2, hfirst, hs, G2Affine.ofWire,
    G2Affine.toWire, G2Affine.add, sourceFp2]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
