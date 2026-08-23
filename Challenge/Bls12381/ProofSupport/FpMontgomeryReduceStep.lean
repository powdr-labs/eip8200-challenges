import Challenge.Bls12381.ProofSupport.FpMontgomeryCarry

set_option warningAsError true

/-!
# BLS12-381 CIOS reduction schedule

This module records the remainder of one source `Reduce` block after the
already-verified low-word cancellation and carry.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

/-- Full `m * n₁` product in the exact source operand order. -/
def montgomeryReductionHighProduct (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.WideProduct :=
  Challenge.EvmProof.Limbs.fullMul256
    (montgomeryReductionMultiplier state) modulusHi

/-- Exact source `s := add(t₁, lo); c₁ := lt(s, t₁)`. -/
def montgomeryReductionHighSum (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.WordSum :=
  Challenge.EvmProof.Limbs.addTwo256 state.t1
    (montgomeryReductionHighProduct state).lo

/-- Exact source `s₂ := add(s, carry); c₂ := lt(s₂, s)`. -/
def montgomeryReductionShiftedSum (state : MontgomeryState) :
    Challenge.EvmProof.Limbs.WordSum :=
  Challenge.EvmProof.Limbs.addTwo256
    (montgomeryReductionHighSum state).word
    (montgomeryReductionCarry state)

/-- The exact source reduction assignment, including the nested final `ADD`s
and explicit clearing of `t₂`. -/
def montgomeryReduceStep (state : MontgomeryState) : MontgomeryState :=
  let highProduct := montgomeryReductionHighProduct state
  let highSum := montgomeryReductionHighSum state
  let shiftedSum := montgomeryReductionShiftedSum state
  { t0 := shiftedSum.word
    t1 := state.t2 +
      (highProduct.hi + (highSum.carry + shiftedSum.carry))
    t2 := UInt256.ofNat 0 }

end Challenge.Bls12381.ProofSupport.Fp
