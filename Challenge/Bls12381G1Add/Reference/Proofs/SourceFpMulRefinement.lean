import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulResult
import Challenge.Bls12381.ProofSupport.FpRepresentation

set_option warningAsError true
set_option maxHeartbeats 100000

/-! # Native G1ADD `fpMul` result boundary -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics.EVM

def convFpMulWide (value : FpMulWideValue) :
    Challenge.EvmProof.Limbs.WideProduct :=
  { hi := YulEvmCompiler.conv value.hi, lo := YulEvmCompiler.conv value.lo }

def convFpMulSum (value : FpMulSumValue) :
    Challenge.EvmProof.Limbs.WordSum :=
  { word := YulEvmCompiler.conv value.word
    carry := YulEvmCompiler.conv value.carry }

theorem conv_fpMulAddTwo (x y : U256) :
    convFpMulSum (fpMulAddTwo x y) =
      Challenge.EvmProof.Limbs.addTwo256
        (YulEvmCompiler.conv x) (YulEvmCompiler.conv y) := by
  rw [Challenge.EvmProof.Limbs.WordSum.mk.injEq]
  constructor
  · simp only [convFpMulSum, fpMulAddTwo,
      Challenge.EvmProof.Limbs.addTwo256]
    rw [YulEvmCompiler.conv_add]
  · simp only [convFpMulSum, fpMulAddTwo,
      Challenge.EvmProof.Limbs.addTwo256]
    rw [YulEvmCompiler.conv_lt, YulEvmCompiler.conv_add]

theorem conv_fpMulAddTerm (sum : FpMulSumValue) (term : U256) :
    convFpMulSum (fpMulAddTerm sum term) =
      Challenge.Bls12381.ProofSupport.Fp.barrettAddTerm
        (convFpMulSum sum) (YulEvmCompiler.conv term) := by
  rw [Challenge.EvmProof.Limbs.WordSum.mk.injEq]
  constructor
  · simp only [convFpMulSum, fpMulAddTerm,
      Challenge.Bls12381.ProofSupport.Fp.barrettAddTerm]
    rw [YulEvmCompiler.conv_add]
  · simp only [convFpMulSum, fpMulAddTerm,
      Challenge.Bls12381.ProofSupport.Fp.barrettAddTerm]
    rw [YulEvmCompiler.conv_add, YulEvmCompiler.conv_lt,
      YulEvmCompiler.conv_add]

private theorem conv_barrettMu0 :
    YulEvmCompiler.conv (BitVec.ofNat 256
      0xad397b918f6ff20d533b6c08511c60e2757079ace6bd401859778ceb4dabc4f8) =
      Challenge.Bls12381.ProofSupport.Fp.barrettMu0 := by
  rw [YulEvmCompiler.conv_eq_ofNat]
  rfl

private theorem conv_barrettMu1 :
    YulEvmCompiler.conv (BitVec.ofNat 256
      0x1b82741ff6a0a94bdf4771e0286779d3997167a058f1c07b13e207f56591ba2e) =
      Challenge.Bls12381.ProofSupport.Fp.barrettMu1 := by
  rw [YulEvmCompiler.conv_eq_ofNat]
  rfl

private theorem conv_barrettMu2 :
    YulEvmCompiler.conv (BitVec.ofNat 256
      0x9d835d2f3cc9e45ce28101b0cc7a6ba29) =
      Challenge.Bls12381.ProofSupport.Fp.barrettMu2 := by
  rw [YulEvmCompiler.conv_eq_ofNat]
  rfl

theorem conv_fpMulBarrettL1 (product : FullMulValue) :
    convFpMulSum (fpMulBarrettL1 product) =
      Challenge.Bls12381.ProofSupport.Fp.barrettL1
        (Challenge.Bls12381.ProofSupport.Fp.barrettPartials
          (convFullMul product)) := by
  simp only [fpMulBarrettL1, fpMulBarrettProducts,
    Challenge.Bls12381.ProofSupport.Fp.barrettL1,
    Challenge.Bls12381.ProofSupport.Fp.barrettPartials, convFullMul]
  rw [conv_fpMulAddTerm, conv_fpMulAddTwo,
    conv_fullWordValue_hi, conv_fullWordValue_lo,
    conv_fullWordValue_lo, conv_barrettMu0, conv_barrettMu1]

private theorem conv_fpMulBarrettL1_carry (product : FullMulValue) :
    YulEvmCompiler.conv (fpMulBarrettL1 product).carry =
      (Challenge.Bls12381.ProofSupport.Fp.barrettL1
        (Challenge.Bls12381.ProofSupport.Fp.barrettPartials
          (convFullMul product))).carry :=
  congrArg Challenge.EvmProof.Limbs.WordSum.carry
    (conv_fpMulBarrettL1 product)

theorem conv_fpMulBarrettL2 (product : FullMulValue) :
    convFpMulSum (fpMulBarrettL2 product) =
      Challenge.Bls12381.ProofSupport.Fp.barrettL2
        (Challenge.Bls12381.ProofSupport.Fp.barrettPartials
          (convFullMul product)) := by
  simp only [fpMulBarrettL2, fpMulBarrettProducts,
    Challenge.Bls12381.ProofSupport.Fp.barrettL2,
    Challenge.Bls12381.ProofSupport.Fp.barrettPartials, convFullMul]
  repeat rw [conv_fpMulAddTerm]
  rw [conv_fpMulAddTwo, conv_fpMulBarrettL1_carry]
  repeat rw [conv_fullWordValue_hi]
  repeat rw [conv_fullWordValue_lo]
  rw [conv_barrettMu0, conv_barrettMu1, conv_barrettMu2]
  rfl

private theorem conv_fpMulBarrettL2_carry (product : FullMulValue) :
    YulEvmCompiler.conv (fpMulBarrettL2 product).carry =
      (Challenge.Bls12381.ProofSupport.Fp.barrettL2
        (Challenge.Bls12381.ProofSupport.Fp.barrettPartials
          (convFullMul product))).carry :=
  congrArg Challenge.EvmProof.Limbs.WordSum.carry
    (conv_fpMulBarrettL2 product)

theorem conv_fpMulBarrettL3 (product : FullMulValue) :
    convFpMulSum (fpMulBarrettL3 product) =
      Challenge.Bls12381.ProofSupport.Fp.barrettL3
        (Challenge.Bls12381.ProofSupport.Fp.barrettPartials
          (convFullMul product)) := by
  simp only [fpMulBarrettL3, fpMulBarrettProducts,
    Challenge.Bls12381.ProofSupport.Fp.barrettL3,
    Challenge.Bls12381.ProofSupport.Fp.barrettPartials, convFullMul]
  repeat rw [conv_fpMulAddTerm]
  rw [conv_fpMulAddTwo, conv_fpMulBarrettL2_carry]
  repeat rw [conv_fullWordValue_hi]
  repeat rw [conv_fullWordValue_lo]
  rw [conv_barrettMu1, conv_barrettMu2]
  rfl

private theorem conv_fpMulBarrettL3_word (product : FullMulValue) :
    YulEvmCompiler.conv (fpMulBarrettL3 product).word =
      (Challenge.Bls12381.ProofSupport.Fp.barrettL3
        (Challenge.Bls12381.ProofSupport.Fp.barrettPartials
          (convFullMul product))).word :=
  congrArg Challenge.EvmProof.Limbs.WordSum.word
    (conv_fpMulBarrettL3 product)

private theorem conv_fpMulBarrettL3_carry (product : FullMulValue) :
    YulEvmCompiler.conv (fpMulBarrettL3 product).carry =
      (Challenge.Bls12381.ProofSupport.Fp.barrettL3
        (Challenge.Bls12381.ProofSupport.Fp.barrettPartials
          (convFullMul product))).carry :=
  congrArg Challenge.EvmProof.Limbs.WordSum.carry
    (conv_fpMulBarrettL3 product)

private theorem fpMulBarrettQuotient_hi (product : FullMulValue) :
    (fpMulBarrettQuotient product).hi =
      (fullWordValue product.r2 (BitVec.ofNat 256
        0x9d835d2f3cc9e45ce28101b0cc7a6ba29)).hi +
        (fpMulBarrettL3 product).carry := by
  rfl

private theorem fpMulBarrettQuotient_lo (product : FullMulValue) :
    (fpMulBarrettQuotient product).lo =
      (fpMulBarrettL3 product).word := by
  rfl

theorem conv_fpMulBarrettQuotient (product : FullMulValue) :
    convFpMulWide (fpMulBarrettQuotient product) =
      Challenge.Bls12381.ProofSupport.Fp.quotientWords
        (convFullMul product) := by
  rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
  constructor
  · simp only [convFpMulWide,
      Challenge.Bls12381.ProofSupport.Fp.quotientWords,
      Challenge.Bls12381.ProofSupport.Fp.barrettQuotient]
    rw [fpMulBarrettQuotient_hi, YulEvmCompiler.conv_add,
      conv_fullWordValue_hi,
      conv_barrettMu2, conv_fpMulBarrettL3_carry]
    rfl
  · simp only [convFpMulWide,
      Challenge.Bls12381.ProofSupport.Fp.quotientWords,
      Challenge.Bls12381.ProofSupport.Fp.barrettQuotient]
    rw [fpMulBarrettQuotient_lo, conv_fpMulBarrettL3_word]

theorem conv_fpMulModulusWide :
    convFpMulWide fpMulModulusWide =
      Challenge.Bls12381.ProofSupport.Fp.modulusWide := by
  rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
  constructor <;>
    simp only [convFpMulWide, fpMulModulusWide,
      Challenge.Bls12381.ProofSupport.Fp.modulusWide,
      Challenge.Bls12381.ProofSupport.Fp.modulusHi,
      Challenge.Bls12381.ProofSupport.Fp.modulusLo] <;>
    rw [YulEvmCompiler.conv_eq_ofNat] <;> rfl

theorem conv_fpMulMultipleLow (quotient : FpMulWideValue) :
    convFpMulWide (fpMulMultipleLow quotient) =
      Challenge.EvmProof.Limbs.mulWideLow256
        (convFpMulWide quotient)
        Challenge.Bls12381.ProofSupport.Fp.modulusWide := by
  rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
  constructor
  · simp only [convFpMulWide, fpMulMultipleLow,
      Challenge.EvmProof.Limbs.mulWideLow256]
    repeat rw [YulEvmCompiler.conv_add]
    repeat rw [YulEvmCompiler.conv_mul]
    rw [conv_fullWordValue_hi]
    have hhi := congrArg Challenge.EvmProof.Limbs.WideProduct.hi
      conv_fpMulModulusWide
    have hlo := congrArg Challenge.EvmProof.Limbs.WideProduct.lo
      conv_fpMulModulusWide
    change YulEvmCompiler.conv fpMulModulusWide.hi = _ at hhi
    change YulEvmCompiler.conv fpMulModulusWide.lo = _ at hlo
    rw [hhi, hlo]
  · simp only [convFpMulWide, fpMulMultipleLow,
      Challenge.EvmProof.Limbs.mulWideLow256]
    rw [conv_fullWordValue_lo]
    have hlo := congrArg Challenge.EvmProof.Limbs.WideProduct.lo
      conv_fpMulModulusWide
    change YulEvmCompiler.conv fpMulModulusWide.lo = _ at hlo
    rw [hlo]

theorem conv_fpMulSubWide (a b : FpMulWideValue) :
    convFpMulWide (fpMulSubWide a b) =
      Challenge.EvmProof.Limbs.subWide256
        (convFpMulWide a) (convFpMulWide b) := by
  rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
  constructor
  · simp only [convFpMulWide, fpMulSubWide,
      Challenge.EvmProof.Limbs.subWide256]
    rw [YulEvmCompiler.conv_sub, YulEvmCompiler.conv_sub,
      YulEvmCompiler.conv_lt]
  · simp only [convFpMulWide, fpMulSubWide,
      Challenge.EvmProof.Limbs.subWide256]
    rw [YulEvmCompiler.conv_sub]

theorem conv_fpMulRemainderValue (product : FullMulValue) :
    convFpMulWide (fpMulRemainderValue product) =
      Challenge.Bls12381.ProofSupport.Fp.barrettRemainder
        (convFullMul product) := by
  unfold fpMulRemainderValue
  rw [conv_fpMulSubWide, conv_fpMulMultipleLow,
    conv_fpMulBarrettQuotient]
  rfl

private theorem fpMulCondition_zero_iff (remainder : FpMulWideValue) :
    fpGeModulusValue remainder.hi remainder.lo = 0 ↔
      (Challenge.EvmProof.Limbs.wideGeWord (convFpMulWide remainder)
        Challenge.Bls12381.ProofSupport.Fp.modulusWide).toNat = 0 := by
  change fpGeModulusValue remainder.hi remainder.lo = 0 ↔
    (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv remainder.hi,
        lo := YulEvmCompiler.conv remainder.lo }).toNat = 0
  constructor
  · intro hzero
    have hconv := conv_fpGeModulusValue remainder.hi remainder.lo
    rw [hzero] at hconv
    have hnat := congrArg UInt256.toNat hconv
    rw [YulEvmCompiler.conv_toNat] at hnat
    exact hnat.symm
  · intro hzero
    rw [← YulEvmCompiler.conv_inj, conv_fpGeModulusValue]
    apply Challenge.EvmProof.Word.word_ext
    rw [YulEvmCompiler.conv_toNat, show (0 : U256).toNat = 0 by decide]
    exact hzero

theorem conv_fpMulCorrectOnce (remainder : FpMulWideValue) :
    convFpMulWide (fpMulCorrectOnce remainder) =
      Challenge.Bls12381.ProofSupport.Fp.barrettCorrectOnce
        (convFpMulWide remainder) := by
  unfold fpMulCorrectOnce
  unfold Challenge.Bls12381.ProofSupport.Fp.barrettCorrectOnce
  by_cases hzero : fpGeModulusValue remainder.hi remainder.lo = 0
  · rw [if_pos hzero, if_neg]
    exact fun hne => hne ((fpMulCondition_zero_iff remainder).mp hzero)
  · rw [if_neg hzero, if_pos]
    · rw [Challenge.Bls12381.ProofSupport.Fp.barrettSubModulus_eq_subWide256,
        conv_fpMulSubWide, conv_fpMulModulusWide]
    · exact fun h => hzero ((fpMulCondition_zero_iff remainder).mpr h)

theorem conv_fpReduceProductValue (product : FullMulValue) :
    convFpMulWide (fpReduceProductValue product) =
      Challenge.Bls12381.ProofSupport.Fp.barrettReduce
        (convFullMul product) := by
  unfold fpReduceProductValue
  unfold Challenge.Bls12381.ProofSupport.Fp.barrettReduce
  rw [conv_fpMulCorrectOnce, conv_fpMulCorrectOnce,
    conv_fpMulRemainderValue]

theorem conv_fpMulResultGraph (ahi alo bhi blo : U256) :
    convFpMulWide (fpMulResultGraph ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.barrettReduce
        (convFullMul (fullMulValue ahi alo bhi blo)) := by
  calc
    convFpMulWide (fpMulResultGraph ahi alo bhi blo) =
        convFpMulWide
          (fpReduceProductValue (fullMulValue ahi alo bhi blo)) :=
      congrArg convFpMulWide (fpMulResultGraph_spec ahi alo bhi blo)
    _ = _ := conv_fpReduceProductValue (fullMulValue ahi alo bhi blo)

def fpMulOutputLimbs (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).1
    lo := YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).2 }

def fpMulLeft (ahi alo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }

def fpMulRight (bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }

private theorem fpMulOutputLimbs_graph (yst : EvmState)
    (ahi alo bhi blo : U256) :
    fpMulOutputLimbs yst ahi alo bhi blo =
      Challenge.Bls12381.ProofSupport.Fp.ofWide
        (convFpMulWide (fpMulResultGraph ahi alo bhi blo)) := by
  rw [Challenge.Bls12381.ProofSupport.Fp.Limbs.mk.injEq]
  constructor
  · simp only [fpMulOutputLimbs,
      Challenge.Bls12381.ProofSupport.Fp.ofWide, convFpMulWide]
    exact congrArg YulEvmCompiler.conv
      (fpMulResult_hi_graph yst ahi alo bhi blo)
  · simp only [fpMulOutputLimbs,
      Challenge.Bls12381.ProofSupport.Fp.ofWide, convFpMulWide]
    exact congrArg YulEvmCompiler.conv
      (fpMulResult_lo_graph yst ahi alo bhi blo)

/-- The parsed native word graph is exactly the shared source-faithful
canonical multiplication schedule. -/
theorem fpMulOutput_eq_mulCanonical_source (yst : EvmState)
    (ahi alo bhi blo : U256) :
    fpMulOutputLimbs yst ahi alo bhi blo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fpMulLeft ahi alo) (fpMulRight bhi blo) := by
  rw [fpMulOutputLimbs_graph, conv_fpMulResultGraph, conv_fullMulValue]
  rfl

theorem fpMulOutput_value (yst : EvmState) (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical (fpMulRight bhi blo)) :
    Challenge.Bls12381.ProofSupport.Fp.value
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      (Challenge.Bls12381.ProofSupport.Fp.value (fpMulLeft ahi alo) *
        Challenge.Bls12381.ProofSupport.Fp.value (fpMulRight bhi blo)) %
          EvmSemantics.Crypto.Bls12381.p := by
  rw [fpMulOutput_eq_mulCanonical_source]
  exact Challenge.Bls12381.ProofSupport.Fp.value_mulCanonical ha hb

theorem canonical_fpMulOutput (yst : EvmState) (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical (fpMulRight bhi blo)) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulOutputLimbs yst ahi alo bhi blo) := by
  rw [fpMulOutput_eq_mulCanonical_source]
  exact Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical ha hb

theorem fpMulOutput_toField (yst : EvmState) (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical (fpMulRight bhi blo)) :
    Challenge.Bls12381.ProofSupport.Fp.toField
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.toField (fpMulLeft ahi alo) *
        Challenge.Bls12381.ProofSupport.Fp.toField (fpMulRight bhi blo) := by
  rw [fpMulOutput_eq_mulCanonical_source]
  exact Challenge.Bls12381.ProofSupport.Fp.toField_mulCanonical ha hb

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
