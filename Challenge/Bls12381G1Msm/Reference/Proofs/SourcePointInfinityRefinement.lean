import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointInfinityExec

set_option warningAsError true

/-! Exact meaning of the frozen G1MSM infinity encoding check. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointInfinityResult_eq_one_iff (yst : EvmState) (ptr : U256) :
    pointInfinityResult yst ptr = 1 ↔
      pointInfinityWords yst ptr = (0, 0, 0, 0) := by
  rcases hwords : pointInfinityWords yst ptr with ⟨xhi, xlo, yhi, ylo⟩
  simp only [pointInfinityResult, hwords, fpZeroValue]
  by_cases hxhi : xhi = 0 <;> by_cases hxlo : xlo = 0 <;>
    by_cases hyhi : yhi = 0 <;> by_cases hylo : ylo = 0 <;>
    simp_all [b2w]

theorem pointInfinityResult_eq_zero_iff (yst : EvmState) (ptr : U256) :
    pointInfinityResult yst ptr = 0 ↔
      pointInfinityWords yst ptr ≠ (0, 0, 0, 0) := by
  rcases hwords : pointInfinityWords yst ptr with ⟨xhi, xlo, yhi, ylo⟩
  simp only [pointInfinityResult, hwords, fpZeroValue]
  by_cases hxhi : xhi = 0 <;> by_cases hxlo : xlo = 0 <;>
    by_cases hyhi : yhi = 0 <;> by_cases hylo : ylo = 0 <;>
    simp_all [b2w]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
