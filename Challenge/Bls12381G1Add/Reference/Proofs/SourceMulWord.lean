import Challenge.Bls12381G1Add.Reference.Proofs.SourceMulDefs
import Challenge.Bls12381.ProofSupport.FpSchoolbook

set_option warningAsError true

/-! # Frozen G1ADD word-product refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics.EVM

/-- Convert a source-word pair to the generic EVM wide-product boundary. -/
def convFullWord (product : FullWordValue) : Challenge.EvmProof.Limbs.WideProduct :=
  { hi := YulEvmCompiler.conv product.hi, lo := YulEvmCompiler.conv product.lo }

/-- Convert a source middle-word accumulator to the generic boundary. -/
def convFullMulMiddle (middle : FullMulMiddleValue) :
    Challenge.EvmProof.Limbs.WordSum :=
  { word := YulEvmCompiler.conv middle.word
    carry := YulEvmCompiler.conv middle.carry }

/-- One frozen `MUL`/`MULMOD` idiom is exactly the shared full-word product. -/
theorem conv_fullWordValue (a b : U256) :
    convFullWord (fullWordValue a b) =
      Challenge.EvmProof.Limbs.fullMul256
        (YulEvmCompiler.conv a) (YulEvmCompiler.conv b) := by
  rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
  constructor <;>
    simp only [convFullWord, fullWordValue, mulModMersenneValue,
      Challenge.EvmProof.Limbs.fullMul256]
  · rw [YulEvmCompiler.conv_sub, YulEvmCompiler.conv_sub,
      YulEvmCompiler.conv_lt, YulEvmCompiler.conv_mul]
    rw [if_neg (show (~~~(0 : U256)) ≠ 0 by decide)]
    have hmm := YulEvmCompiler.conv_mulmod a b (~~~(0 : U256))
    rw [if_neg (show (~~~(0 : U256)) ≠ 0 by decide)] at hmm
    have hzero : YulEvmCompiler.conv (0 : U256) = UInt256.ofNat 0 := by
      rw [YulEvmCompiler.conv_eq_ofNat]
      rfl
    rw [hmm, YulEvmCompiler.conv_not, hzero]
  · exact YulEvmCompiler.conv_mul a b

theorem conv_fullWordValue_hi (a b : U256) :
    YulEvmCompiler.conv (fullWordValue a b).hi =
      (Challenge.EvmProof.Limbs.fullMul256
        (YulEvmCompiler.conv a) (YulEvmCompiler.conv b)).hi :=
  congrArg Challenge.EvmProof.Limbs.WideProduct.hi (conv_fullWordValue a b)

theorem conv_fullWordValue_lo (a b : U256) :
    YulEvmCompiler.conv (fullWordValue a b).lo =
      (Challenge.EvmProof.Limbs.fullMul256
        (YulEvmCompiler.conv a) (YulEvmCompiler.conv b)).lo :=
  congrArg Challenge.EvmProof.Limbs.WideProduct.lo (conv_fullWordValue a b)

/-- The two source-ordered middle-word additions are the shared accumulator. -/
theorem conv_fullMulMiddleValue (x y z : U256) :
    convFullMulMiddle (fullMulMiddleValue x y z) =
      Challenge.EvmProof.Limbs.addThree256
        (YulEvmCompiler.conv x) (YulEvmCompiler.conv y)
          (YulEvmCompiler.conv z) := by
  rw [Challenge.EvmProof.Limbs.WordSum.mk.injEq]
  constructor
  · simp only [convFullMulMiddle, fullMulMiddleValue,
      Challenge.EvmProof.Limbs.addThree256]
    rw [YulEvmCompiler.conv_add, YulEvmCompiler.conv_add]
  · simp only [convFullMulMiddle, fullMulMiddleValue,
      Challenge.EvmProof.Limbs.addThree256]
    rw [YulEvmCompiler.conv_add, YulEvmCompiler.conv_lt,
      YulEvmCompiler.conv_lt]
    repeat rw [YulEvmCompiler.conv_add]

theorem conv_fullMulMiddleValue_word (x y z : U256) :
    YulEvmCompiler.conv (fullMulMiddleValue x y z).word =
      (Challenge.EvmProof.Limbs.addThree256
        (YulEvmCompiler.conv x) (YulEvmCompiler.conv y)
          (YulEvmCompiler.conv z)).word :=
  congrArg Challenge.EvmProof.Limbs.WordSum.word
    (conv_fullMulMiddleValue x y z)

theorem conv_fullMulMiddleValue_carry (x y z : U256) :
    YulEvmCompiler.conv (fullMulMiddleValue x y z).carry =
      (Challenge.EvmProof.Limbs.addThree256
        (YulEvmCompiler.conv x) (YulEvmCompiler.conv y)
          (YulEvmCompiler.conv z)).carry :=
  congrArg Challenge.EvmProof.Limbs.WordSum.carry
    (conv_fullMulMiddleValue x y z)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
