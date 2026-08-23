import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteUnequalExec

set_option warningAsError true

/-! # G1ADD unequal-x slope refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev LawfulFp := PrimeField.LawfulFp

private def limbsOfWords (words : U256 × U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv words.1, lo := YulEvmCompiler.conv words.2 }

def mainFiniteUnequalX1 (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainDecodedWord yst 0, mainDecodedWord yst 32)

def mainFiniteUnequalY1 (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainDecodedWord yst 64, mainDecodedWord yst 96)

def mainFiniteUnequalX2 (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainDecodedWord yst 128, mainDecodedWord yst 160)

def mainFiniteUnequalY2 (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainDecodedWord yst 192, mainDecodedWord yst 224)

def mainFiniteUnequalNumerator (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainFiniteUnequalNumeratorWords yst)

def mainFiniteUnequalDenominator (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainFiniteUnequalDenominatorWords yst)

def mainFiniteUnequalDenInv (yst : EvmState) : Fp.Limbs :=
  fpInvOutputLimbs (mainFiniteUnequalDenominatorArgsState yst)
    (mainFiniteUnequalDenominatorWords yst).1
    (mainFiniteUnequalDenominatorWords yst).2

def mainFiniteUnequalLambda (yst : EvmState) : Fp.Limbs :=
  fpMulOutputLimbs (mainFiniteUnequalState1 yst)
    (mainFiniteUnequalNumeratorWords yst).1
    (mainFiniteUnequalNumeratorWords yst).2
    (mainFiniteUnequalDenInvWords yst).1
    (mainFiniteUnequalDenInvWords yst).2

private def toLawful (a : Fp.Limbs) : LawfulFp :=
  PrimeField.finEquiv (Fp.toField a)

private theorem numerator_eq (yst : EvmState) :
    mainFiniteUnequalNumerator yst =
      Fp.subSource (mainFiniteUnequalY2 yst)
        (mainFiniteUnequalY1 yst) :=
  conv_fpSubValue _ _ _ _

private theorem denominator_eq (yst : EvmState) :
    mainFiniteUnequalDenominator yst =
      Fp.subSource (mainFiniteUnequalX2 yst)
        (mainFiniteUnequalX1 yst) :=
  conv_fpSubValue _ _ _ _

private theorem denInv_eq (yst : EvmState)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst)) :
    mainFiniteUnequalDenInv yst =
      Fp.invCanonical (mainFiniteUnequalDenominator yst) := by
  apply fpInvOutput_eq_invCanonical
  change Fp.Canonical (mainFiniteUnequalDenominator yst)
  rw [denominator_eq]
  exact Fp.canonical_subSource hx2 hx1

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

theorem mainFiniteUnequalLambda_eq (yst : EvmState)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hy1 : Fp.Canonical (mainFiniteUnequalY1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst))
    (hy2 : Fp.Canonical (mainFiniteUnequalY2 yst)) :
    mainFiniteUnequalLambda yst =
      Fp.mulCanonical (mainFiniteUnequalNumerator yst)
        (mainFiniteUnequalDenInv yst) := by
  apply fpMulOutput_eq_mulCanonical
  · change Fp.Canonical (mainFiniteUnequalNumerator yst)
    rw [numerator_eq]
    exact Fp.canonical_subSource hy2 hy1
  · change Fp.Canonical (mainFiniteUnequalDenInv yst)
    rw [denInv_eq yst hx1 hx2, denominator_eq]
    exact Fp.canonical_invCanonical (Fp.canonical_subSource hx2 hx1)

theorem canonical_mainFiniteUnequalLambda (yst : EvmState)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hy1 : Fp.Canonical (mainFiniteUnequalY1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst))
    (hy2 : Fp.Canonical (mainFiniteUnequalY2 yst)) :
    Fp.Canonical (mainFiniteUnequalLambda yst) := by
  rw [mainFiniteUnequalLambda_eq yst hx1 hy1 hx2 hy2]
  apply Fp.canonical_mulCanonical
  · rw [numerator_eq]
    exact Fp.canonical_subSource hy2 hy1
  · rw [denInv_eq yst hx1 hx2, denominator_eq]
    exact Fp.canonical_invCanonical (Fp.canonical_subSource hx2 hx1)

private theorem lawful_subSource {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    toLawful (Fp.subSource a b) = toLawful a - toLawful b := by
  have h := congrArg PrimeField.finEquiv (Fp.toField_subSource ha hb)
  simpa only [toLawful, map_sub] using h

private theorem lawful_mulCanonical {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    toLawful (Fp.mulCanonical a b) = toLawful a * toLawful b := by
  have h := congrArg PrimeField.finEquiv (Fp.toField_mulCanonical ha hb)
  simpa only [toLawful, map_mul] using h

private theorem lawful_invCanonical {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    toLawful (Fp.invCanonical a) = (toLawful a)⁻¹ := by
  simpa only [toLawful, Fp.finEquiv_toField] using Fp.lawful_invCanonical ha

/-- The exact source lambda is the lawful general-addition slope. -/
theorem mainFiniteUnequalLambda_toLawful (yst : EvmState)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hy1 : Fp.Canonical (mainFiniteUnequalY1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst))
    (hy2 : Fp.Canonical (mainFiniteUnequalY2 yst))
    (_hne : toLawful (mainFiniteUnequalX1 yst) ≠
      toLawful (mainFiniteUnequalX2 yst)) :
    PrimeField.finEquiv (Fp.toField (mainFiniteUnequalLambda yst)) =
      (PrimeField.finEquiv (Fp.toField (mainFiniteUnequalY2 yst)) -
        PrimeField.finEquiv (Fp.toField (mainFiniteUnequalY1 yst))) /
      (PrimeField.finEquiv (Fp.toField (mainFiniteUnequalX2 yst)) -
        PrimeField.finEquiv (Fp.toField (mainFiniteUnequalX1 yst))) := by
  change toLawful (mainFiniteUnequalLambda yst) =
    (toLawful (mainFiniteUnequalY2 yst) -
      toLawful (mainFiniteUnequalY1 yst)) /
    (toLawful (mainFiniteUnequalX2 yst) -
      toLawful (mainFiniteUnequalX1 yst))
  have hnum := Fp.canonical_subSource hy2 hy1
  have hden := Fp.canonical_subSource hx2 hx1
  have hdenInv := Fp.canonical_invCanonical hden
  rw [mainFiniteUnequalLambda_eq yst hx1 hy1 hx2 hy2,
    lawful_mulCanonical (by rw [numerator_eq]; exact hnum)
      (by rw [denInv_eq yst hx1 hx2, denominator_eq]; exact hdenInv),
    numerator_eq, lawful_subSource hy2 hy1,
    denInv_eq yst hx1 hx2, lawful_invCanonical (by
      rw [denominator_eq]; exact hden),
    denominator_eq, lawful_subSource hx2 hx1]
  rfl

theorem step_mainFiniteUnequal_canonical (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 0)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteUnequalStmt (mainFiniteUnequalResultEnv yst)
      (mainFiniteUnequalFinalState yst) .normal := by
  apply step_mainFiniteUnequal yst hxeq
  change (mainFiniteUnequalDenominator yst).hi.toNat < 2 ^ 128
  rw [denominator_eq]
  exact (Fp.canonical_subSource hx2 hx1).1

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
