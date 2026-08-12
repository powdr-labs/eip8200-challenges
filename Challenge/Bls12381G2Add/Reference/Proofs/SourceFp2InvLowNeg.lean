import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowReal

set_option warningAsError true

/-! # Low-memory preservation through Fp2 inverse negation reads -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvAfterNegReads_loadWord_low (yst : EvmState)
    (out a : U256) (offset : Nat) (hend : offset + 32 ≤ 1024)
    (houtHigh : 1024 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2InvAfterNegReads yst out a).memory offset =
      loadWord yst.memory offset := by
  rw [fp2InvAfterNegReads_memory]
  exact fp2InvAfterRealStores_loadWord_low yst out a offset hend houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
