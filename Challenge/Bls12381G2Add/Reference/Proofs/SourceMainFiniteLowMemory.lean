import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvLowFinal

set_option warningAsError true

/-! # Low-coordinate preservation through G2ADD finite arithmetic

Each arithmetic call is discharged against its opaque memory-preservation
endpoint.  The staged theorems keep the complete nested Fp2 execution graph
out of the final consumers.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem mainDoubleState0_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainDoubleState0 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainDoubleState0]
  exact (fp2MulFinalState_fp2At_before_scratch _ _ _ _ _ hptrEnd hptrLow
    (by decide) (by decide)).trans
      (mainAfterDoubleYZero_fp2At yst ptr)

theorem mainDoubleState1_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainDoubleState1 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainDoubleState1]
  exact (fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) hptrEnd (by bv_omega)).trans
      (mainDoubleState0_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainDoubleState2_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainDoubleState2 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainDoubleState2]
  exact (fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) hptrEnd (by bv_omega)).trans
      (mainDoubleState1_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainDoubleState3_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainDoubleState3 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainDoubleState3]
  exact (fp2AddContractState_fp2At_before_out _ _ _ _ _
    (by decide) hptrEnd (by bv_omega)).trans
      (mainDoubleState2_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainDoubleState4_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainDoubleState4 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainDoubleState4]
  exact (fp2InvFinalState_fp2At_before_scratch _ _ _ _ hptrEnd hptrLow
    (by decide) (by decide)).trans
      (mainDoubleState3_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainDoubleFinalState_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainDoubleFinalState yst) ptr =
      fp2At (mainValidatedState yst) ptr := by
  rw [mainDoubleFinalState]
  exact (fp2MulFinalState_fp2At_before_scratch _ _ _ _ _ hptrEnd hptrLow
    (by decide) (by decide)).trans
      (mainDoubleState4_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainAfterDoubleXEq2_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainAfterDoubleXEq2 yst) ptr =
      fp2At (mainValidatedState yst) ptr :=
  (mainAfterDoubleXEq2_fp2At yst ptr).trans
    (mainDoubleFinalState_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainFiniteUnequalState0_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainUnequalState0 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainUnequalState0]
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _ hptrEnd
    (by bv_omega) (by decide)).trans
      (mainAfterFiniteXEq2_fp2At yst ptr)

theorem mainUnequalState1_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainUnequalState1 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainUnequalState1]
  exact (fp2SubFinalState_fp2At_before_out _ _ _ _ _ hptrEnd
    (by bv_omega) (by decide)).trans
      (mainFiniteUnequalState0_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainUnequalState2_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainUnequalState2 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainUnequalState2]
  exact (fp2InvFinalState_fp2At_before_scratch _ _ _ _ hptrEnd hptrLow
    (by decide) (by decide)).trans
      (mainUnequalState1_fp2At_low yst ptr hptrEnd hptrLow)

theorem mainUnequalFinalState_fp2At_low (yst : EvmState) (ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024) :
    fp2At (mainUnequalFinalState yst) ptr =
      fp2At (mainValidatedState yst) ptr := by
  rw [mainUnequalFinalState]
  exact (fp2MulFinalState_fp2At_before_scratch _ _ _ _ _ hptrEnd hptrLow
    (by decide) (by decide)).trans
      (mainUnequalState2_fp2At_low yst ptr hptrEnd hptrLow)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
