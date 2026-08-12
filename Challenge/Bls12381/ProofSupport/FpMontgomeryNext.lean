import Challenge.Bls12381.ProofSupport.FpMontgomeryFirst

set_option warningAsError true

/-! # Second BLS12-381 CIOS product accumulation schedule -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

def montgomeryNextLowProduct (x1 : UInt256) (y : Limbs) :
    Challenge.EvmProof.Limbs.WideProduct :=
  Challenge.EvmProof.Limbs.fullMul256 x1 y.lo

def montgomeryNextLowSum (state : MontgomeryState) (x1 : UInt256)
    (y : Limbs) : Challenge.EvmProof.Limbs.WordSum :=
  Challenge.EvmProof.Limbs.addTwo256 state.t0 (montgomeryNextLowProduct x1 y).lo

/-- Exact source `carry := add(hi, lt(s,t₀))`. -/
def montgomeryNextCarry (state : MontgomeryState) (x1 : UInt256)
    (y : Limbs) : UInt256 :=
  (montgomeryNextLowProduct x1 y).hi + (montgomeryNextLowSum state x1 y).carry

def montgomeryNextHighProduct (x1 : UInt256) (y : Limbs) :
    Challenge.EvmProof.Limbs.WideProduct :=
  Challenge.EvmProof.Limbs.fullMul256 x1 y.hi

/-- Exact source `s := add(t₁, lo); c₁ := lt(s, t₁)`. -/
def montgomeryNextHighSum (state : MontgomeryState) (x1 : UInt256)
    (y : Limbs) : Challenge.EvmProof.Limbs.WordSum :=
  Challenge.EvmProof.Limbs.addTwo256 state.t1
    (montgomeryNextHighProduct x1 y).lo

/-- Exact source `s₂ := add(s, carry); c₂ := lt(s₂, s)`. -/
def montgomeryNextShiftedSum (state : MontgomeryState) (x1 : UInt256)
    (y : Limbs) : Challenge.EvmProof.Limbs.WordSum :=
  Challenge.EvmProof.Limbs.addTwo256 (montgomeryNextHighSum state x1 y).word
    (montgomeryNextCarry state x1 y)

/-- Exact product-accumulation half of source iteration `i = 1`. -/
def montgomeryAccumulateNext (state : MontgomeryState) (x1 : UInt256)
    (y : Limbs) : MontgomeryState :=
  let lowSum := montgomeryNextLowSum state x1 y
  let highProduct := montgomeryNextHighProduct x1 y
  let highSum := montgomeryNextHighSum state x1 y
  let shiftedSum := montgomeryNextShiftedSum state x1 y
  { t0 := lowSum.word
    t1 := shiftedSum.word
    t2 := highProduct.hi + (highSum.carry + shiftedSum.carry) }

end Challenge.Bls12381.ProofSupport.Fp
