import Challenge.Bls12381G1Add.Reference.Proofs.SourceMulWord

set_option warningAsError true

/-! # Frozen G1ADD full-multiplication refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics.EVM

/-- Convert the source-word result into the shared three-word product type. -/
def convFullMul (product : FullMulValue) :
    Challenge.Bls12381.ProofSupport.Fp.SchoolbookProduct :=
  { r2 := YulEvmCompiler.conv product.r2
    r1 := YulEvmCompiler.conv product.r1
    r0 := YulEvmCompiler.conv product.r0 }

/-- The frozen source full-multiply graph is the shared source-faithful
schoolbook schedule. -/
theorem conv_fullMulValue (ahi alo bhi blo : U256) :
    convFullMul (fullMulValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } := by
  rw [Challenge.Bls12381.ProofSupport.Fp.SchoolbookProduct.mk.injEq]
  constructor
  · simp only [convFullMul, fullMulValue,
      Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct]
    repeat rw [YulEvmCompiler.conv_add]
    rw [YulEvmCompiler.conv_mul]
    repeat rw [conv_fullWordValue_hi]
    rw [conv_fullMulMiddleValue_carry]
    repeat rw [conv_fullWordValue_hi]
    repeat rw [conv_fullWordValue_lo]
  · constructor
    · simp only [convFullMul, fullMulValue,
        Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct]
      rw [conv_fullMulMiddleValue_word]
      repeat rw [conv_fullWordValue_hi]
      repeat rw [conv_fullWordValue_lo]
    · simp only [convFullMul, fullMulValue,
        Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct]
      rw [conv_fullWordValue_lo]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
