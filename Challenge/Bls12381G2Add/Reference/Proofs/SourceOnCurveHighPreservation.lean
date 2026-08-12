import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveRhs

set_option warningAsError true

/-! # High-memory preservation for frozen G2ADD Fp2 products -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulFinalState_loadWord_before_out_high
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hstart : 1920 ≤ offset) (hend : offset + 32 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2MulFinalState yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulFinalState, fp2MulAfterImagHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterImagReads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat (fp2MulImag yst out a b).1)
      (out + BitVec.ofNat 256 96).toNat (fp2MulImag yst out a b).2) offset = _
  rw [loadWord_storeWord_disjoint _
      (out + BitVec.ofNat 256 96).toNat offset _ (by right; bv_omega),
    loadWord_storeWord_disjoint _
      (out + BitVec.ofNat 256 64).toNat offset _ (by right; bv_omega)]
  have hreads : (fp2MulAfterImagReads yst out a b).memory =
      (fp2MulAfterVSumStores yst out a b).memory := rfl
  rw [hreads, fp2MulAfterVSumStores_loadWord_high _ _ _ _ offset hstart]
  exact fp2MulAfterRealStores_loadWord_before_out yst out a b offset
    (by omega) hend (by omega)

theorem fp2MulFinalState_fp2At_before_out_high
    (yst : EvmState) (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hbefore : ptr.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2MulFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    exact fp2MulFinalState_loadWord_before_out_high yst out a b _
      (by bv_omega) (by bv_omega) houtEnd

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
