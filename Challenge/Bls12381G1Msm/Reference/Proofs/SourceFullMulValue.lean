import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulDefs
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMul

set_option warningAsError true

/-! Arithmetic value boundary for the frozen G1MSM `fullMul` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

abbrev FullMulValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.FullMulValue

abbrev fullMulValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fullMulValue

abbrev convFullMul :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.convFullMul

theorem conv_fullMulValue (ahi alo bhi blo : U256) :
    convFullMul (fullMulValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } := by
  exact
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullMulValue
      ahi alo bhi blo

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
