import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowNeg

set_option warningAsError true

/-! # Low-memory preservation through Fp2 inverse imaginary reads -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem twoTouches_memory (st : EvmState) (first second : Nat) :
    (touchMemory (touchMemory st first 32) second 32).memory = st.memory := rfl

theorem fp2InvAfterImagReads_loadWord_low (yst : EvmState)
    (out a : U256) (offset : Nat) (hend : offset + 32 ≤ 1024)
    (houtHigh : 1024 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2InvAfterImagReads yst out a).memory offset =
      loadWord yst.memory offset := by
  have hmem := twoTouches_memory (fp2InvAfterNegReads yst out a) 1696 1664
  change (fp2InvAfterImagReads yst out a).memory =
    (fp2InvAfterNegReads yst out a).memory at hmem
  rw [hmem]
  exact fp2InvAfterNegReads_loadWord_low yst out a offset hend houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
