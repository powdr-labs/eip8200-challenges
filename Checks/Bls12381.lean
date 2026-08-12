import Challenge.Bls12381
import Checks.Bls12381CodecFp
import Checks.Bls12381CodecFp2
import Checks.Bls12381CodecScalar
import Checks.Bls12381CodecG1
import Checks.Bls12381CodecG2
import Checks.Bls12381CodecRepresentation
import Checks.Bls12381CodecSubgroup
import Checks.Bls12381CodecConformance
import Checks.Bls12381FpRepresentation
import Checks.Bls12381FpPredicates
import Checks.Bls12381FpWordBridge
import Checks.Bls12381FpAddSubSchedule
import Checks.Bls12381FpAdd
import Checks.Bls12381FpAddSub
import Checks.Bls12381FpNeg
import Checks.Bls12381FpAddSubLawful
import Checks.Bls12381FpBarrettSchedule
import Checks.Bls12381FpBarrett
import Checks.Bls12381FpBarrettSubtract
import Checks.Bls12381FpBarrettReduce
import Checks.Bls12381FpMul
import Checks.Bls12381FpMontgomery
import Checks.Bls12381FpMontgomeryPow
import Checks.Bls12381FpInvConstants
import Checks.Bls12381FpInv
import Checks.Bls12381FpSqrtLawful
import Checks.Bls12381FpSqrtConstants
import Checks.Bls12381FpSqrt
import Checks.Bls12381Fp2Representation
import Checks.Bls12381Fp2SourceSchedule
import Checks.Bls12381Fp2SourceCanonical
import Checks.Bls12381Fp2SourceLawful
import Checks.Bls12381Fp2SourceMul
import Checks.Bls12381Fp2SourceInv
import Checks.Bls12381Fp2Predicates
import Checks.Bls12381Fp2SqrtConstants
import Checks.Bls12381Fp2SqrtProgram
import Checks.Bls12381Fp2SqrtLawfulOps
import Checks.Bls12381Fp2SqrtRefinement
import Checks.Bls12381Fp2SqrtLawful
import Checks.Bls12381Fp2Sqrt
import Checks.Bls12381LawfulAffine
import Checks.Bls12381AffineGroup
import Checks.Bls12381AffineGroupBls
import Checks.Bls12381G1Affine
import Checks.Bls12381G2Affine
import Checks.Bls12381LawfulAffineConformance
import Checks.Bls12381ScalarMul
import Checks.Bls12381ScalarMulConformance
import Checks.Bls12381Msm
import Checks.Bls12381MsmSemantics
import Checks.Bls12381MsmSubgroup
import Checks.Bls12381MsmConformance
import Checks.Bls12381SswuCore
import Checks.Bls12381MapToG1Support
import Checks.Bls12381MapToG1SqrtRatio
import Checks.Bls12381MapToG1IsogenyIdentity
import Checks.Bls12381MapToG1Isogeny
import Checks.Bls12381MapToG1Executable
import Checks.Bls12381MapToG1Map
import Checks.Bls12381MapToG2Support
import Checks.Bls12381MapToG2SqrtRatio
import Checks.Bls12381MapToG2Isogeny
import Checks.Bls12381MapToG2IsogenyIdentity
import Checks.Bls12381MapToG2IsogenyLawful
import Checks.Bls12381MapToG2Map
import Checks.Bls12381Subgroup
import Checks.Bls12381SubgroupSemantics

set_option warningAsError true

/-!
# Shared BLS12-381 proof-support checks

This target keeps the family-level support independently buildable. Individual
challenge correctness theorems have their own axiom-footprint checks.
-/

#print axioms Challenge.Bls12381.ProofSupport.Codec.decodeFp_encodeFp

#print axioms Challenge.Bls12381.ProofSupport.Fp.value_ofField
#print axioms Challenge.Bls12381.ProofSupport.Fp.value_normalize
#print axioms Challenge.Bls12381.ProofSupport.Fp.refines_add
#print axioms Challenge.Bls12381.ProofSupport.Fp2.mul_components
#print axioms Challenge.Bls12381.ProofSupport.Fp2.refines_mul
#print axioms Challenge.Bls12381.ProofSupport.Fp6.mul_components
#print axioms Challenge.Bls12381.ProofSupport.Fp6.refines_mul
#print axioms Challenge.Bls12381.ProofSupport.Fp12.mul_components
#print axioms Challenge.Bls12381.ProofSupport.Fp12.refines_mul
#print axioms Challenge.Bls12381.ProofSupport.G1Projective.affine_toAffine
#print axioms Challenge.Bls12381.ProofSupport.G2Projective.affine_toAffine
#print axioms Challenge.Bls12381.ProofSupport.ScalarMul.g1_onCurve
#print axioms Challenge.Bls12381.ProofSupport.ScalarMul.g2_onCurve
