import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowScalar

set_option warningAsError true

/-! # Low-memory preservation through Fp2 inverse real output -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvAfterRealStores_loadWord_low (yst : EvmState) (out a : U256)
    (offset : Nat) (hend : offset + 32 ≤ 1024)
    (houtHigh : 1024 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2InvAfterRealStores yst out a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvAfterRealStores fp2InvAfterRealHigh
  change loadWord (storeWord (storeWord (fp2InvAfterRealCall yst a).memory
    out.toNat _) (out + BitVec.ofNat 256 32).toNat _) offset = _
  rw [loadWord_storeWord_disjoint _ _ offset _ (by right; bv_omega),
    loadWord_storeWord_disjoint _ out.toNat offset _ (by right; omega)]
  unfold fp2InvAfterRealCall
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend,
    fp2InvAfterRealReads, fp2AddReadState_memory,
    fp2InvAfterScalarStores_loadWord_low yst a offset hend]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
