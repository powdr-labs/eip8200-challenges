import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowImagCall

set_option warningAsError true

/-! # Final Fp2 inverse stores preserve low memory -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvFinalState_loadWord_before_scratch (yst : EvmState)
    (out a : U256) (offset : Nat) (hend : offset + 32 ≤ 1024)
    (houtHigh : 1024 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2InvFinalState yst out a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvFinalState fp2InvAfterImagHigh
  change loadWord (storeWord (storeWord (fp2InvAfterImagCall yst out a).memory
    (out + BitVec.ofNat 256 64).toNat _)
    (out + BitVec.ofNat 256 96).toNat _) offset = _
  rw [loadWord_storeWord_disjoint _ _ offset _ (by right; bv_omega),
    loadWord_storeWord_disjoint _ _ offset _ (by right; bv_omega)]
  exact fp2InvAfterImagCall_loadWord_low yst out a offset hend houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
