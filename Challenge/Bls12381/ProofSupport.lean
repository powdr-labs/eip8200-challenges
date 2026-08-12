import Challenge.Bls12381.ProofSupport.Codec
import Challenge.Bls12381.ProofSupport.CodecFp
import Challenge.Bls12381.ProofSupport.CodecFp2
import Challenge.Bls12381.ProofSupport.CodecScalar
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.CodecRepresentation
import Challenge.Bls12381.ProofSupport.CodecSubgroup
import Challenge.Bls12381.ProofSupport.Fp
import Challenge.Bls12381.ProofSupport.FpRepresentation
import Challenge.Bls12381.ProofSupport.FpPredicates
import Challenge.Bls12381.ProofSupport.FpConstants
import Challenge.Bls12381.ProofSupport.FpWordBridge
import Challenge.Bls12381.ProofSupport.FpAddSub
import Challenge.Bls12381.ProofSupport.FpAddSubLawful
import Challenge.Bls12381.ProofSupport.FpSchoolbook
import Challenge.Bls12381.ProofSupport.FpBarrettSchedule
import Challenge.Bls12381.ProofSupport.FpBarrett
import Challenge.Bls12381.ProofSupport.FpBarrettSubtract
import Challenge.Bls12381.ProofSupport.FpBarrettReduce
import Challenge.Bls12381.ProofSupport.FpMul
import Challenge.Bls12381.ProofSupport.FpSquare
import Challenge.Bls12381.ProofSupport.FpMontgomeryLawful
import Challenge.Bls12381.ProofSupport.FpMontgomeryPowLawful
import Challenge.Bls12381.ProofSupport.FpInvConstants
import Challenge.Bls12381.ProofSupport.FpInv
import Challenge.Bls12381.ProofSupport.FpSqrtLawful
import Challenge.Bls12381.ProofSupport.FpSqrtConstants
import Challenge.Bls12381.ProofSupport.FpSqrt
import Challenge.Bls12381.ProofSupport.FpParity
import Challenge.Bls12381.ProofSupport.LawfulFp2
import Challenge.Bls12381.ProofSupport.Fp2
import Challenge.Bls12381.ProofSupport.Fp2Representation
import Challenge.Bls12381.ProofSupport.Fp2SourceDefs
import Challenge.Bls12381.ProofSupport.Fp2SourceProgram
import Challenge.Bls12381.ProofSupport.Fp2SourcePrimitives
import Challenge.Bls12381.ProofSupport.Fp2SourceSchedule
import Challenge.Bls12381.ProofSupport.Fp2Source
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful
import Challenge.Bls12381.ProofSupport.Fp2Predicates
import Challenge.Bls12381.ProofSupport.Fp2SqrtConstants
import Challenge.Bls12381.ProofSupport.Fp2SqrtProgram
import Challenge.Bls12381.ProofSupport.Fp2SqrtDefs
import Challenge.Bls12381.ProofSupport.Fp2SqrtLawfulOps
import Challenge.Bls12381.ProofSupport.Fp2SqrtRefinement
import Challenge.Bls12381.ProofSupport.Fp2SqrtLawful
import Challenge.Bls12381.ProofSupport.Fp2Sqrt
import Challenge.Bls12381.ProofSupport.LawfulFp6
import Challenge.Bls12381.ProofSupport.LawfulFp6Norm
import Challenge.Bls12381.ProofSupport.Fp6
import Challenge.Bls12381.ProofSupport.LawfulFp12
import Challenge.Bls12381.ProofSupport.LawfulFp12Norm
import Challenge.Bls12381.ProofSupport.Fp12
import Challenge.Bls12381.ProofSupport.LawfulAffine
import Challenge.Bls12381.ProofSupport.AffineGroup
import Challenge.Bls12381.ProofSupport.G1Affine
import Challenge.Bls12381.ProofSupport.G2Affine
import Challenge.Bls12381.ProofSupport.AffineGroupBls
import Challenge.Bls12381.ProofSupport.G1Projective
import Challenge.Bls12381.ProofSupport.G2Projective
import Challenge.Bls12381.ProofSupport.ScalarMulProgram
import Challenge.Bls12381.ProofSupport.ScalarMul
import Challenge.Bls12381.ProofSupport.ScalarMulSemantics
import Challenge.Bls12381.ProofSupport.Msm
import Challenge.Bls12381.ProofSupport.MsmSemantics
import Challenge.Bls12381.ProofSupport.MsmSubgroup
import Challenge.Bls12381.ProofSupport.MapPolynomial
import Challenge.Bls12381.ProofSupport.MapPolynomialLawful
import Challenge.Bls12381.ProofSupport.SswuCore
import Challenge.Bls12381.ProofSupport.SswuCoreLawful
import Challenge.Bls12381.ProofSupport.MapToG1
import Challenge.Bls12381.ProofSupport.MapToG1SqrtRatio
import Challenge.Bls12381.ProofSupport.MapToG1Sswu
import Challenge.Bls12381.ProofSupport.MapToG1Isogeny
import Challenge.Bls12381.ProofSupport.MapToG1IsogenyIdentity
import Challenge.Bls12381.ProofSupport.MapToG1IsogenyLawful
import Challenge.Bls12381.ProofSupport.MapToG1Executable
import Challenge.Bls12381.ProofSupport.MapToG1Map
import Challenge.Bls12381.ProofSupport.MapToG2
import Challenge.Bls12381.ProofSupport.MapToG2SqrtRatioDefs
import Challenge.Bls12381.ProofSupport.MapToG2SqrtRatio
import Challenge.Bls12381.ProofSupport.MapToG2Isogeny
import Challenge.Bls12381.ProofSupport.MapToG2IsogenyIdentity
import Challenge.Bls12381.ProofSupport.MapToG2IsogenyLawful
import Challenge.Bls12381.ProofSupport.MapToG2Executable
import Challenge.Bls12381.ProofSupport.MapToG2Map
import Challenge.Bls12381.ProofSupport.PrimeField
import Challenge.Bls12381.ProofSupport.PrimeCertificate
import Challenge.Bls12381.ProofSupport.Subgroup
import Challenge.Bls12381.ProofSupport.SubgroupSemantics

set_option warningAsError true

/-!
# BLS12-381 family proof support

Only facts shared by more than one EIP-2537 challenge belong under this
umbrella. It may depend on generic EVM proof support and the pinned crypto
semantics, but never on an individual challenge.
-/
