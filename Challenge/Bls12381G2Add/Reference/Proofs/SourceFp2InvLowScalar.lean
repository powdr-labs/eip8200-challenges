import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowSquare1

set_option warningAsError true

/-! # Low-memory preservation through Fp2 scalar inversion -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvAfterScalarStores_loadWord_low (yst : EvmState) (a : U256)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (fp2InvAfterScalarStores yst a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvAfterScalarStores fp2InvAfterScalarHigh
  change loadWord (storeWord (storeWord (fp2InvAfterScalarCall yst a).memory
    1664 _) 1696 _) offset = _
  rw [loadWord_storeWord_disjoint _ 1696 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1664 offset _ (by omega)]
  unfold fp2InvAfterScalarCall
  rw [fpInvFinalState_loadWord_before_scratch _ _ _ offset hend,
    fp2InvAfterNormReads, fp2AddReadState_memory,
    fp2InvAfterSquare1Stores_loadWord_low yst a offset hend]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
