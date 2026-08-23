import Challenge.Bls12381G1Add.Reference.Proofs.SourceSub

set_option warningAsError true

/-! # Frozen G1ADD full-multiplication helper values -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM

/-- The source-level low/high result of one EVM-word full multiplication. -/
structure FullWordValue where
  hi : U256
  lo : U256

/-- The exact `MULMOD (2^256 - 1)` expression used by the frozen helper. -/
def mulModMersenneValue (a b : U256) : U256 :=
  let modulus := ~~~(0 : U256)
  if modulus = 0 then 0
  else BitVec.ofNat 256 ((a.toNat * b.toNat) % modulus.toNat)

/-- One exact `MUL`/`MULMOD` full-word product from the frozen source. -/
def fullWordValue (a b : U256) : FullWordValue :=
  let lo := a * b
  let mm := mulModMersenneValue a b
  { hi := mm - lo - b2w (BitVec.ult mm lo), lo := lo }

/-- The source-level three-word result of multiplying two decoded Fp values. -/
structure FullMulValue where
  r2 : U256
  r1 : U256
  r0 : U256

/-- Result word and the sum of the two source-ordered overflow tests. -/
structure FullMulMiddleValue where
  word : U256
  carry : U256

/-- Exact two-`ADD` middle-word accumulator from the frozen helper. -/
def fullMulMiddleValue (x y z : U256) : FullMulMiddleValue :=
  let first := x + y
  let firstCarry := b2w (BitVec.ult first x)
  let result := first + z
  let carry := firstCarry + b2w (BitVec.ult result first)
  { word := result, carry }

/-- Exact value graph of the frozen `fullMul` helper, including its two
source-ordered middle-word carry tests. -/
def fullMulValue (ahi alo bhi blo : U256) : FullMulValue :=
  let p00 := fullWordValue alo blo
  let p10 := fullWordValue ahi blo
  let p01 := fullWordValue alo bhi
  let middle := fullMulMiddleValue p00.hi p10.lo p01.lo
  { r2 := p10.hi + p01.hi + (ahi * bhi + middle.carry)
    r1 := middle.word
    r0 := p00.lo }

/-- The seventh frozen helper evaluates to the exact three-word source graph. -/
theorem eval_fullMul (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x006" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fullMulValue ahi alo bhi blo).r2,
      (fullMulValue ahi alo bhi blo).r1,
      (fullMulValue ahi alo bhi blo).r0] yst) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
