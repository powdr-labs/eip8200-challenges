import Challenge.Bls12381G2Add.Reference.Proofs.SourceCopyPointMemory

set_option warningAsError true

/-! # X-coordinate projection of the frozen G2ADD point copy helper -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem copyPointState_256_fp2At_x (yst : EvmState) :
    fp2At (copyPointState yst 256) 0 = fp2At yst 256 := by
  unfold fp2At
  norm_num
  constructor
  · constructor
    · change loadWord (copyPointState yst 256).memory 0 =
        loadWord yst.memory 256
      exact copyPointState_256_word0 yst
    · change loadWord (copyPointState yst 256).memory 32 =
        loadWord yst.memory 288
      exact copyPointState_256_word1 yst
  · constructor
    · change loadWord (copyPointState yst 256).memory 64 =
        loadWord yst.memory 320
      exact copyPointState_256_word2 yst
    · change loadWord (copyPointState yst 256).memory 96 =
        loadWord yst.memory 352
      exact copyPointState_256_word3 yst

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
