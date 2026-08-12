import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowFinalWord

set_option warningAsError true

/-! # Fp2-level low-memory preservation through inversion -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2InvFinalState_fp2At_before_scratch (yst : EvmState)
    (out a ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024)
    (houtHigh : 1024 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2InvFinalState yst out a) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    exact fp2InvFinalState_loadWord_before_scratch yst out a _
      (by bv_omega) houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
