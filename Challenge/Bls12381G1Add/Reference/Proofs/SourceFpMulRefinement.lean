import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulBody
import Challenge.Bls12381.ProofSupport.FpRepresentation

set_option warningAsError true

/-! # Native G1ADD `fpMul` result boundary -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

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

/-- The opaque wrapper result is exactly the parsed native reduction graph. -/
theorem fpMulResultValue_sourceGraph (ahi alo bhi blo : U256) :
    fpMulResultValue ahi alo bhi blo =
      ((fpReduceProductValue (fullMulValue ahi alo bhi blo)).hi,
        (fpReduceProductValue (fullMulValue ahi alo bhi blo)).lo) :=
  fpMulResultValue_spec ahi alo bhi blo

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
