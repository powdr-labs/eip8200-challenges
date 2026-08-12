import Challenge.Bls12381.ProofSupport.CodecFp
import Challenge.Bls12381.ProofSupport.CodecFp2
import Challenge.Bls12381.ProofSupport.CodecScalar
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.CodecRepresentation
import Challenge.Bls12381.ProofSupport.CodecSubgroup

set_option warningAsError true

/-!
# Shared EIP-2537 codec compatibility umbrella

Declarations live in their domain modules.  This file only reexports the
split API for existing callers that imported the former monolith.
-/
