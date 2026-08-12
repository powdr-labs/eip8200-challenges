import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowSquare0

set_option warningAsError true

/-! # Low-memory preservation through Fp2 inversion square one -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvAfterSquare1Stores_loadWord_low (yst : EvmState) (a : U256)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (fp2InvAfterSquare1Stores yst a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvAfterSquare1Stores fp2InvAfterSquare1High
  change loadWord (storeWord (storeWord (fp2InvAfterSquare1Call yst a).memory
    1600 _) 1632 _) offset = _
  rw [loadWord_storeWord_disjoint _ 1632 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1600 offset _ (by omega)]
  unfold fp2InvAfterSquare1Call
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend,
    fp2InvAfterSquare1Reads, fp2AddReadState_memory,
    fp2InvAfterSquare0Stores_loadWord_low yst a offset hend]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
