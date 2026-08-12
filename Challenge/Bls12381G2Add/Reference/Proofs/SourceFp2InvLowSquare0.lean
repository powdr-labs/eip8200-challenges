import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvPreservation

set_option warningAsError true

/-! # Low-memory preservation through Fp2 inversion square zero -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvAfterSquare0Stores_loadWord_low (yst : EvmState) (a : U256)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (fp2InvAfterSquare0Stores yst a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvAfterSquare0Stores fp2InvAfterSquare0High
  change loadWord (storeWord (storeWord (fp2InvAfterSquare0Call yst a).memory
    1536 _) 1568 _) offset = _
  rw [loadWord_storeWord_disjoint _ 1568 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1536 offset _ (by omega)]
  unfold fp2InvAfterSquare0Call
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend,
    fp2InvAfterSquare0Reads, fp2AddReadState_memory]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
