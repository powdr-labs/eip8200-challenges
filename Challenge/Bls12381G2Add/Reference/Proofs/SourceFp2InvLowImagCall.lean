import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowImagReads

set_option warningAsError true

/-! # Low-memory preservation through Fp2 inverse imaginary multiplication -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvAfterImagCall_loadWord_low (yst : EvmState)
    (out a : U256) (offset : Nat) (hend : offset + 32 ≤ 1024)
    (houtHigh : 1024 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2InvAfterImagCall yst out a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvAfterImagCall
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend]
  exact fp2InvAfterImagReads_loadWord_low yst out a offset hend houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
