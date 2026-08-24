import Challenge.Bls12381G1Add.Reference.Proofs.SourceMul
import Challenge.Bls12381.ProofSupport.FpMul

set_option warningAsError true
set_option maxRecDepth 4096

/-! # Frozen G1ADD native multiplication values -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM

/-- A source-word low/high pair. -/
structure FpMulWideValue where
  hi : U256
  lo : U256

/-- A wrapped source word together with its accumulated carry word. -/
structure FpMulSumValue where
  word : U256
  carry : U256

def fpMulAddTwo (x y : U256) : FpMulSumValue :=
  let word := x + y
  { word, carry := b2w (BitVec.ult word x) }

def fpMulAddTerm (sum : FpMulSumValue) (term : U256) : FpMulSumValue :=
  let word := sum.word + term
  { word, carry := sum.carry + b2w (BitVec.ult word term) }

def fpMulBarrettProducts (product : FullMulValue) :
    FullWordValue × FullWordValue × FullWordValue ×
      FullWordValue × FullWordValue × FullWordValue :=
  let m0 := BitVec.ofNat 256
    0xad397b918f6ff20d533b6c08511c60e2757079ace6bd401859778ceb4dabc4f8
  let m1 := BitVec.ofNat 256
    0x1b82741ff6a0a94bdf4771e0286779d3997167a058f1c07b13e207f56591ba2e
  let m2 := BitVec.ofNat 256 0x9d835d2f3cc9e45ce28101b0cc7a6ba29
  (fullWordValue product.r1 m0, fullWordValue product.r1 m1,
    fullWordValue product.r1 m2, fullWordValue product.r2 m0,
    fullWordValue product.r2 m1, fullWordValue product.r2 m2)

def fpMulBarrettL1 (product : FullMulValue) : FpMulSumValue :=
  let ps := fpMulBarrettProducts product
  fpMulAddTerm (fpMulAddTwo ps.1.hi ps.2.1.lo) ps.2.2.2.1.lo

def fpMulBarrettL2 (product : FullMulValue) : FpMulSumValue :=
  let ps := fpMulBarrettProducts product
  fpMulAddTerm
    (fpMulAddTerm
      (fpMulAddTerm (fpMulAddTwo ps.2.1.hi ps.2.2.2.1.hi) ps.2.2.1.lo)
      ps.2.2.2.2.1.lo)
    (fpMulBarrettL1 product).carry

def fpMulBarrettL3 (product : FullMulValue) : FpMulSumValue :=
  let ps := fpMulBarrettProducts product
  fpMulAddTerm
    (fpMulAddTerm (fpMulAddTwo ps.2.2.1.hi ps.2.2.2.2.1.hi)
      ps.2.2.2.2.2.lo)
    (fpMulBarrettL2 product).carry

/-- Exact source-word graph for the fixed Barrett quotient. -/
def fpMulBarrettQuotient (product : FullMulValue) : FpMulWideValue :=
  let products := fpMulBarrettProducts product
  let p12 := products.2.2.2.2.2
  let l3 := fpMulBarrettL3 product
  { hi := p12.hi + l3.carry, lo := l3.word }

def fpMulModulusWide : FpMulWideValue :=
  { hi := BitVec.ofNat 256 0x1a0111ea397fe69a4b1ba7b6434bacd7
    lo := BitVec.ofNat 256
      0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab }

def fpMulMultipleLow (quotient : FpMulWideValue) : FpMulWideValue :=
  let low := fullWordValue quotient.lo fpMulModulusWide.lo
  { hi := low.hi + quotient.lo * fpMulModulusWide.hi +
      quotient.hi * fpMulModulusWide.lo
    lo := low.lo }

def fpMulSubWide (a b : FpMulWideValue) : FpMulWideValue :=
  { hi := a.hi - b.hi - b2w (BitVec.ult a.lo b.lo)
    lo := a.lo - b.lo }

def fpMulCorrectOnce (remainder : FpMulWideValue) : FpMulWideValue :=
  if fpGeModulusValue remainder.hi remainder.lo = 0 then remainder
  else fpMulSubWide remainder fpMulModulusWide

/-- Exact source-word graph before the two Barrett corrections. -/
def fpMulRemainderValue (product : FullMulValue) : FpMulWideValue :=
  let quotient := fpMulBarrettQuotient product
  fpMulSubWide { hi := product.r1, lo := product.r0 }
    (fpMulMultipleLow quotient)

/-- Exact source-word graph of `fpReduceProduct`, including both corrections. -/
def fpReduceProductValue (product : FullMulValue) : FpMulWideValue :=
  fpMulCorrectOnce (fpMulCorrectOnce (fpMulRemainderValue product))

/-- An opaque wrapper result together with its checked source-graph equation. -/
structure FpMulResultContract where
  value : U256 → U256 → U256 → U256 → U256 × U256
  refines : ∀ ahi alo bhi blo,
    value ahi alo bhi blo =
      ((fpReduceProductValue (fullMulValue ahi alo bhi blo)).hi,
        (fpReduceProductValue (fullMulValue ahi alo bhi blo)).lo)

opaque fpMulResultContract : FpMulResultContract :=
  { value := fun ahi alo bhi blo =>
      let reduced := fpReduceProductValue (fullMulValue ahi alo bhi blo)
      (reduced.hi, reduced.lo)
    refines := by intro ahi alo bhi blo; rfl }

/-- Pure native multiplication result, kept opaque at wrapper boundaries. -/
def fpMulResultValue (ahi alo bhi blo : U256) : U256 × U256 :=
  fpMulResultContract.value ahi alo bhi blo

def fpMulResultHi (ahi alo bhi blo : U256) : U256 :=
  (fpMulResultValue ahi alo bhi blo).1

def fpMulResultLo (ahi alo bhi blo : U256) : U256 :=
  (fpMulResultValue ahi alo bhi blo).2

theorem fpMulResultValue_spec (ahi alo bhi blo : U256) :
    fpMulResultValue ahi alo bhi blo =
      ((fpReduceProductValue (fullMulValue ahi alo bhi blo)).hi,
        (fpReduceProductValue (fullMulValue ahi alo bhi blo)).lo) :=
  fpMulResultContract.refines ahi alo bhi blo


/-- Native multiplication result in the source theorem interface. -/
def fpMulResult (_yst : EvmState) (ahi alo bhi blo : U256) : U256 × U256 :=
  fpMulResultValue ahi alo bhi blo

/-- Native multiplication leaves the EVM state unchanged. -/
def fpMulFinalState (yst : EvmState) (_ahi _alo _bhi _blo : U256) : EvmState :=
  yst

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
