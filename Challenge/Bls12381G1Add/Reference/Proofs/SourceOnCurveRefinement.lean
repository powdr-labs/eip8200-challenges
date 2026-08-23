import Challenge.Bls12381G1Add.Reference.Proofs.SourceOnCurveExec
import Challenge.Bls12381.ProofSupport.FpMul
import Challenge.Bls12381.ProofSupport.FpPredicates
import Challenge.Bls12381.ProofSupport.G1Affine

set_option warningAsError true

/-! # Frozen G1ADD `onCurve` refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def limbsOfWords (words : U256 × U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv words.1, lo := YulEvmCompiler.conv words.2 }

def onCurveLhs (yst : EvmState) (yHi yLo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  limbsOfWords (onCurveLhsWords yst yHi yLo)

def onCurveX2 (yst : EvmState) (xHi xLo yHi yLo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  limbsOfWords (onCurveX2Words yst xHi xLo yHi yLo)

def onCurveRhsCube (yst : EvmState) (xHi xLo yHi yLo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  limbsOfWords (onCurveRhsCubeWords yst xHi xLo yHi yLo)

def onCurveRhs (yst : EvmState) (xHi xLo yHi yLo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  limbsOfWords (onCurveRhsWords yst xHi xLo yHi yLo)

def onCurveFour : Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := 0, lo := 4 }

theorem canonical_onCurveFour :
    Challenge.Bls12381.ProofSupport.Fp.Canonical onCurveFour := by
  apply Challenge.Bls12381.ProofSupport.Fp.canonical_of_value_lt
  change 4 + Challenge.EvmProof.Limbs.radix * 0 <
    EvmSemantics.Crypto.Bls12381.p
  norm_num [Challenge.EvmProof.Limbs.radix,
    EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

private theorem fpMulOutput_eq_mulCanonical (yst : EvmState)
    (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulRight bhi blo)) :
    fpMulOutputLimbs yst ahi alo bhi blo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fpMulLeft ahi alo) (fpMulRight bhi blo) := by
  apply Challenge.Bls12381.ProofSupport.Fp.limbs_ext_of_value_eq
  rcases Challenge.Bls12381.ProofSupport.Fp.mulCanonical_spec ha hb with
    ⟨hcanonical, hshared⟩
  apply Challenge.Bls12381.ProofSupport.Fp.value_eq_of_lawful_eq
    (canonical_fpMulOutput yst ahi alo bhi blo)
    hcanonical
  have hfield := fpMulOutput_toField yst ahi alo bhi blo ha hb
  have hfin := hfield.trans hshared.symm
  change Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
      (Challenge.Bls12381.ProofSupport.Fp.toField
        (fpMulOutputLimbs yst ahi alo bhi blo)) =
    Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
      (Challenge.Bls12381.ProofSupport.Fp.toField
        (Challenge.Bls12381.ProofSupport.Fp.mulCanonical
          (fpMulLeft ahi alo) (fpMulRight bhi blo)))
  exact congrArg Challenge.Bls12381.ProofSupport.PrimeField.finEquiv hfin

theorem onCurveLhs_eq (yst : EvmState) (yHi yLo : U256)
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveY yHi yLo)) :
    onCurveLhs yst yHi yLo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (onCurveY yHi yLo) (onCurveY yHi yLo) := by
  exact fpMulOutput_eq_mulCanonical yst yHi yLo yHi yLo hy hy

private theorem onCurveX2_eq (yst : EvmState) (xHi xLo yHi yLo : U256)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveX xHi xLo)) :
    onCurveX2 yst xHi xLo yHi yLo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (onCurveX xHi xLo) (onCurveX xHi xLo) := by
  exact fpMulOutput_eq_mulCanonical (onCurveState1 yst yHi yLo)
    xHi xLo xHi xLo hx hx

private theorem onCurveRhsCube_eq (yst : EvmState)
    (xHi xLo yHi yLo : U256)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveX xHi xLo)) :
    onCurveRhsCube yst xHi xLo yHi yLo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (Challenge.Bls12381.ProofSupport.Fp.mulCanonical
          (onCurveX xHi xLo) (onCurveX xHi xLo))
        (onCurveX xHi xLo) := by
  have hx2 := Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical hx hx
  have h := fpMulOutput_eq_mulCanonical
    (onCurveState2 yst xHi xLo yHi yLo)
    (onCurveX2Words yst xHi xLo yHi yLo).1
    (onCurveX2Words yst xHi xLo yHi yLo).2 xHi xLo
    (canonical_fpMulOutput (onCurveState1 yst yHi yLo) xHi xLo xHi xLo) hx
  change onCurveRhsCube yst xHi xLo yHi yLo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (onCurveX2 yst xHi xLo yHi yLo) (onCurveX xHi xLo) at h
  rw [onCurveX2_eq yst xHi xLo yHi yLo hx] at h
  exact h

theorem onCurveRhs_eq (yst : EvmState) (xHi xLo yHi yLo : U256)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveX xHi xLo)) :
    onCurveRhs yst xHi xLo yHi yLo =
      Challenge.Bls12381.ProofSupport.Fp.addSource
        (Challenge.Bls12381.ProofSupport.Fp.mulCanonical
          (Challenge.Bls12381.ProofSupport.Fp.mulCanonical
            (onCurveX xHi xLo) (onCurveX xHi xLo))
          (onCurveX xHi xLo)) onCurveFour := by
  have hconv := conv_fpAddValue
    (onCurveRhsCubeWords yst xHi xLo yHi yLo).1
    (onCurveRhsCubeWords yst xHi xLo yHi yLo).2 0 4
  change onCurveRhs yst xHi xLo yHi yLo =
      Challenge.Bls12381.ProofSupport.Fp.addSource
        (onCurveRhsCube yst xHi xLo yHi yLo) onCurveFour at hconv
  rw [onCurveRhsCube_eq yst xHi xLo yHi yLo hx] at hconv
  exact hconv

private theorem result_eq_one_iff_words_eq (yst : EvmState)
    (xHi xLo yHi yLo : U256) :
    onCurveResult yst xHi xLo yHi yLo = 1 ↔
      onCurveLhsWords yst yHi yLo =
        onCurveRhsWords yst xHi xLo yHi yLo := by
  rcases hLhs : onCurveLhsWords yst yHi yLo with ⟨lhsHi, lhsLo⟩
  rcases hRhs : onCurveRhsWords yst xHi xLo yHi yLo with ⟨rhsHi, rhsLo⟩
  simp only [onCurveResult, hLhs, hRhs, fpEqValue]
  by_cases hHi : lhsHi = rhsHi <;> by_cases hLo : lhsLo = rhsLo <;>
    simp [b2w, hHi, hLo]

theorem result_eq_one_iff_limbs_eq (yst : EvmState)
    (xHi xLo yHi yLo : U256) :
    onCurveResult yst xHi xLo yHi yLo = 1 ↔
      onCurveLhs yst yHi yLo = onCurveRhs yst xHi xLo yHi yLo := by
  rw [result_eq_one_iff_words_eq]
  simp only [onCurveLhs, onCurveRhs, limbsOfWords]
  constructor
  · intro h; rw [h]
  · intro h
    apply Prod.ext
    · exact YulEvmCompiler.conv_injective (congrArg
        Challenge.Bls12381.ProofSupport.Fp.Limbs.hi h)
    · exact YulEvmCompiler.conv_injective (congrArg
        Challenge.Bls12381.ProofSupport.Fp.Limbs.lo h)

theorem onCurveResult_zero_or_one (yst : EvmState)
    (xHi xLo yHi yLo : U256) :
    onCurveResult yst xHi xLo yHi yLo = 0 ∨
      onCurveResult yst xHi xLo yHi yLo = 1 := by
  rcases hLhs : onCurveLhsWords yst yHi yLo with ⟨lhsHi, lhsLo⟩
  rcases hRhs : onCurveRhsWords yst xHi xLo yHi yLo with ⟨rhsHi, rhsLo⟩
  by_cases hHi : lhsHi = rhsHi <;> by_cases hLo : lhsLo = rhsLo <;>
    simp [onCurveResult, hLhs, hRhs, fpEqValue, b2w, hHi, hLo]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
