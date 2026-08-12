import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXOperands
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalMath

set_option warningAsError true

/-! Field refinement of the unequal slope square. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddUnequalLimbsOfWords (words : U256 × U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv words.1, lo := YulEvmCompiler.conv words.2 }

def pointAddUnequalX3Limbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  pointAddUnequalLimbsOfWords
    (pointAddUnequalX3Result yst out left right)

private theorem fpMulOutput_eq_mulCanonical (yst : EvmState)
    (ahi alo bhi blo : U256) (ha : Fp.Canonical (fpMulLeft ahi alo))
    (hb : Fp.Canonical (fpMulRight bhi blo)) :
    fpMulOutputLimbs yst ahi alo bhi blo =
      Fp.mulCanonical (fpMulLeft ahi alo) (fpMulRight bhi blo) := by
  apply Fp.limbs_ext_of_value_eq
  apply Fp.value_eq_of_lawful_eq
    (canonical_fpMulOutput yst ahi alo bhi blo)
    (Fp.canonical_mulCanonical ha hb)
  have hfield := fpMulOutput_toField yst ahi alo bhi blo ha hb
  have hshared := Fp.toField_mulCanonical ha hb
  have hfin := hfield.trans hshared.symm
  simpa only [Fp.finEquiv_toField] using congrArg PrimeField.finEquiv hfin

theorem pointAddUnequalX3Limbs_eq (yst : EvmState)
    (out left right : U256)
    (hlambda : Fp.Canonical
      (pointAddUnequalLambdaLimbs yst out left right)) :
    pointAddUnequalX3Limbs yst out left right =
      Fp.mulCanonical (pointAddUnequalLambdaLimbs yst out left right)
        (pointAddUnequalLambdaLimbs yst out left right) := by
  unfold pointAddUnequalX3Limbs pointAddUnequalX3Result
  exact fpMulOutput_eq_mulCanonical _ _ _ _ _ hlambda hlambda

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
