import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteDefs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubOutput

set_option warningAsError true

/-! # Read-only finite-branch boundaries for frozen G2ADD -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem mainAfterFiniteXEq1_fp2At (yst : EvmState) (ptr : U256) :
    fp2At (mainAfterFiniteXEq1 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainAfterFiniteXEq1]
  apply fp2At_eq_of_loads <;> all_goals rw [fp2EqReadState_memory]

theorem mainAfterFiniteXEq2_fp2At (yst : EvmState) (ptr : U256) :
    fp2At (mainAfterFiniteXEq2 yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainAfterFiniteXEq2]
  have hread : fp2At (fp2EqReadState (mainAfterFiniteXEq1 yst) 0 256) ptr =
      fp2At (mainAfterFiniteXEq1 yst) ptr := by
    apply fp2At_eq_of_loads <;> all_goals rw [fp2EqReadState_memory]
  exact hread.trans (mainAfterFiniteXEq1_fp2At yst ptr)

theorem mainAfterDoubleYEq_fp2At (yst : EvmState) (ptr : U256) :
    fp2At (mainAfterDoubleYEq yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainAfterDoubleYEq]
  have hread : fp2At (fp2EqReadState (mainAfterFiniteXEq1 yst) 128 384) ptr =
      fp2At (mainAfterFiniteXEq1 yst) ptr := by
    apply fp2At_eq_of_loads <;> all_goals rw [fp2EqReadState_memory]
  exact hread.trans (mainAfterFiniteXEq1_fp2At yst ptr)

theorem mainAfterDoubleYZero_fp2At (yst : EvmState) (ptr : U256) :
    fp2At (mainAfterDoubleYZero yst) ptr = fp2At (mainValidatedState yst) ptr := by
  rw [mainAfterDoubleYZero]
  have hread : fp2At (fp2ReadState (mainAfterDoubleYEq yst) 128) ptr =
      fp2At (mainAfterDoubleYEq yst) ptr := by
    apply fp2At_eq_of_loads <;> all_goals rw [fp2ReadState_memory]
  exact hread.trans (mainAfterDoubleYEq_fp2At yst ptr)

theorem mainAfterDoubleXEq2_fp2At (yst : EvmState) (ptr : U256) :
    fp2At (mainAfterDoubleXEq2 yst) ptr = fp2At (mainDoubleFinalState yst) ptr := by
  rw [mainAfterDoubleXEq2]
  apply fp2At_eq_of_loads <;> all_goals rw [fp2EqReadState_memory]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
