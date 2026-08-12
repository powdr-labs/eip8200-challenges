import Challenge.Bls12381G2Add.Reference.Proofs.SourceCopyPointX

set_option warningAsError true

/-! # Y-coordinate projection of the frozen G2ADD point copy helper -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem copyPointState_256_fp2At_y (yst : EvmState) :
    fp2At (copyPointState yst 256) 128 = fp2At yst 384 := by
  unfold fp2At
  norm_num
  constructor
  · constructor
    · change loadWord (copyPointState yst 256).memory 128 =
        loadWord yst.memory 384
      exact copyPointState_256_word4 yst
    · change loadWord (copyPointState yst 256).memory 160 =
        loadWord yst.memory 416
      exact copyPointState_256_word5 yst
  · constructor
    · change loadWord (copyPointState yst 256).memory 192 =
        loadWord yst.memory 448
      exact copyPointState_256_word6 yst
    · change loadWord (copyPointState yst 256).memory 224 =
        loadWord yst.memory 480
      exact copyPointState_256_word7 yst

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
