import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleExec
import Challenge.Bls12381.ProofSupport.FpInv

set_option warningAsError true

/-! # G1ADD equal-point doubling-slope refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev LawfulFp := PrimeField.LawfulFp

private def limbsOfWords (words : U256 × U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv words.1, lo := YulEvmCompiler.conv words.2 }

def mainFiniteDoubleX (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainFiniteDoubleXWords yst)

def mainFiniteDoubleY (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainFiniteDoubleYWords yst)

def mainFiniteDoubleXSq (yst : EvmState) : Fp.Limbs :=
  fpMulOutputLimbs (mainFiniteDoubleXSqArgsState yst)
    (mainFiniteDoubleXWords yst).1 (mainFiniteDoubleXWords yst).2
    (mainFiniteDoubleXWords yst).1 (mainFiniteDoubleXWords yst).2

def mainFiniteDoubleTwice (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainFiniteDoubleTwiceWords yst)

def mainFiniteDoubleNumerator (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainFiniteDoubleNumeratorWords yst)

def mainFiniteDoubleDenominator (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainFiniteDoubleDenominatorWords yst)

def mainFiniteDoubleDenInv (yst : EvmState) : Fp.Limbs :=
  fpInvOutputLimbs (mainFiniteDoubleDenArgsState yst)
    (mainFiniteDoubleDenominatorWords yst).1
    (mainFiniteDoubleDenominatorWords yst).2

def mainFiniteDoubleLambda (yst : EvmState) : Fp.Limbs :=
  fpMulOutputLimbs (mainFiniteDoubleState2 yst)
    (mainFiniteDoubleNumeratorWords yst).1
    (mainFiniteDoubleNumeratorWords yst).2
    (mainFiniteDoubleDenInvWords yst).1
    (mainFiniteDoubleDenInvWords yst).2

private def toLawful (a : Fp.Limbs) : LawfulFp :=
  Challenge.Bls12381.ProofSupport.PrimeField.finEquiv (Fp.toField a)

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
  simpa only [Fp.finEquiv_toField] using congrArg
    Challenge.Bls12381.ProofSupport.PrimeField.finEquiv hfin

private theorem mainFiniteDoubleXSq_eq (yst : EvmState)
    (hx : Fp.Canonical (mainFiniteDoubleX yst)) :
    mainFiniteDoubleXSq yst =
      Fp.mulCanonical (mainFiniteDoubleX yst) (mainFiniteDoubleX yst) := by
  exact fpMulOutput_eq_mulCanonical _ _ _ _ _ hx hx

private theorem mainFiniteDoubleTwice_eq (yst : EvmState) :
    mainFiniteDoubleTwice yst =
      Fp.addSource (mainFiniteDoubleXSq yst)
        (mainFiniteDoubleXSq yst) := by
  exact conv_fpAddValue _ _ _ _

private theorem mainFiniteDoubleNumerator_eq (yst : EvmState) :
    mainFiniteDoubleNumerator yst =
      Fp.addSource (mainFiniteDoubleTwice yst)
        (mainFiniteDoubleXSq yst) := by
  exact conv_fpAddValue _ _ _ _

private theorem mainFiniteDoubleDenominator_eq (yst : EvmState) :
    mainFiniteDoubleDenominator yst =
      Fp.addSource (mainFiniteDoubleY yst) (mainFiniteDoubleY yst) := by
  exact conv_fpAddValue _ _ _ _

private theorem mainFiniteDoubleDenInv_eq (yst : EvmState)
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    mainFiniteDoubleDenInv yst =
      Fp.invCanonical (mainFiniteDoubleDenominator yst) := by
  apply fpInvOutput_eq_invCanonical
  change Fp.Canonical (mainFiniteDoubleDenominator yst)
  rw [mainFiniteDoubleDenominator_eq]
  exact Fp.canonical_addSource hy hy

theorem mainFiniteDoubleLambda_eq (yst : EvmState)
    (hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    mainFiniteDoubleLambda yst =
      Fp.mulCanonical (mainFiniteDoubleNumerator yst)
        (mainFiniteDoubleDenInv yst) := by
  apply fpMulOutput_eq_mulCanonical
  · change Fp.Canonical (mainFiniteDoubleNumerator yst)
    rw [mainFiniteDoubleNumerator_eq, mainFiniteDoubleTwice_eq,
      mainFiniteDoubleXSq_eq yst hx]
    have hxsq := Fp.canonical_mulCanonical hx hx
    exact Fp.canonical_addSource (Fp.canonical_addSource hxsq hxsq) hxsq
  · change Fp.Canonical (mainFiniteDoubleDenInv yst)
    rw [mainFiniteDoubleDenInv_eq yst hy]
    rw [mainFiniteDoubleDenominator_eq]
    exact Fp.canonical_invCanonical (Fp.canonical_addSource hy hy)

theorem canonical_mainFiniteDoubleLambda (yst : EvmState)
    (hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    Fp.Canonical (mainFiniteDoubleLambda yst) := by
  rw [mainFiniteDoubleLambda_eq yst hx hy]
  apply Fp.canonical_mulCanonical
  · rw [mainFiniteDoubleNumerator_eq, mainFiniteDoubleTwice_eq,
      mainFiniteDoubleXSq_eq yst hx]
    have hxsq := Fp.canonical_mulCanonical hx hx
    exact Fp.canonical_addSource (Fp.canonical_addSource hxsq hxsq) hxsq
  · rw [mainFiniteDoubleDenInv_eq yst hy]
    apply Fp.canonical_invCanonical
    rw [mainFiniteDoubleDenominator_eq]
    exact Fp.canonical_addSource hy hy

/-- Canonical operands discharge the source inversion helper's high-limb
precondition, yielding the complete checked doubling-slope execution. -/
theorem step_mainFiniteDoubleBody_canonical (yst : EvmState)
    (_hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      mainFiniteDoubleBody (mainFiniteDoubleEnv6 yst)
      (mainFiniteDoubleFinalState yst) .normal := by
  apply step_mainFiniteDoubleBody
  change (mainFiniteDoubleDenominator yst).hi.toNat < 2 ^ 128
  rw [mainFiniteDoubleDenominator_eq]
  exact (Fp.canonical_addSource hy hy).1

private theorem lawful_mulCanonical {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    toLawful (Fp.mulCanonical a b) = toLawful a * toLawful b := by
  have h := congrArg PrimeField.finEquiv (Fp.toField_mulCanonical ha hb)
  simpa only [toLawful, map_mul] using h

private theorem lawful_addSource {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    toLawful (Fp.addSource a b) = toLawful a + toLawful b := by
  have h := congrArg Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
    (Fp.toField_addSource ha hb)
  simpa only [toLawful, map_add] using h

private theorem lawful_invCanonical {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    toLawful (Fp.invCanonical a) = (toLawful a)⁻¹ := by
  simpa only [toLawful, Fp.finEquiv_toField] using Fp.lawful_invCanonical ha

/-- The exact source lambda is the lawful affine doubling slope
`3*x² / (2*y)`. -/
theorem mainFiniteDoubleLambda_toLawful (yst : EvmState)
    (hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    PrimeField.finEquiv (Fp.toField (mainFiniteDoubleLambda yst)) =
      (3 * PrimeField.finEquiv (Fp.toField (mainFiniteDoubleX yst)) ^ 2) /
        (2 * PrimeField.finEquiv (Fp.toField (mainFiniteDoubleY yst))) := by
  change toLawful (mainFiniteDoubleLambda yst) =
    (3 * toLawful (mainFiniteDoubleX yst) ^ 2) /
      (2 * toLawful (mainFiniteDoubleY yst))
  have hxsq := Fp.canonical_mulCanonical hx hx
  have htwice := Fp.canonical_addSource hxsq hxsq
  have hnum := Fp.canonical_addSource htwice hxsq
  have hden := Fp.canonical_addSource hy hy
  have hdenInv := Fp.canonical_invCanonical hden
  have hxsqActual : Fp.Canonical (mainFiniteDoubleXSq yst) := by
    rw [mainFiniteDoubleXSq_eq yst hx]
    exact hxsq
  have htwiceActual : Fp.Canonical (mainFiniteDoubleTwice yst) := by
    rw [mainFiniteDoubleTwice_eq]
    exact Fp.canonical_addSource hxsqActual hxsqActual
  have hnumActual : Fp.Canonical (mainFiniteDoubleNumerator yst) := by
    rw [mainFiniteDoubleNumerator_eq]
    exact Fp.canonical_addSource htwiceActual hxsqActual
  have hdenActual : Fp.Canonical (mainFiniteDoubleDenominator yst) := by
    rw [mainFiniteDoubleDenominator_eq]
    exact Fp.canonical_addSource hy hy
  have hdenInvActual : Fp.Canonical (mainFiniteDoubleDenInv yst) := by
    rw [mainFiniteDoubleDenInv_eq yst hy]
    exact Fp.canonical_invCanonical hdenActual
  rw [mainFiniteDoubleLambda_eq yst hx hy,
    lawful_mulCanonical hnumActual hdenInvActual,
    mainFiniteDoubleNumerator_eq,
    lawful_addSource htwiceActual hxsqActual,
    mainFiniteDoubleTwice_eq,
    lawful_addSource hxsqActual hxsqActual,
    mainFiniteDoubleXSq_eq yst hx,
    lawful_mulCanonical hx hx,
    mainFiniteDoubleDenInv_eq yst hy,
    lawful_invCanonical hdenActual,
    mainFiniteDoubleDenominator_eq,
    lawful_addSource hy hy]
  ring

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
