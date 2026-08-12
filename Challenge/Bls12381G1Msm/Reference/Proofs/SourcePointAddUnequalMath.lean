import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointMemoryReady
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvRefinement

set_option warningAsError true

/-! Lawful refinement of the unequal-x G1MSM slope. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev LawfulFp := PrimeField.LawfulFp

private def limbsOfWords (words : U256 × U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv words.1, lo := YulEvmCompiler.conv words.2 }

def pointAddUnequalY1 (yst : EvmState) (out left right : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddUnequalLeftYHi yst out left right)
    lo := YulEvmCompiler.conv (pointAddUnequalLeftYLo yst out left right) }

def pointAddUnequalY2 (yst : EvmState) (out left right : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddUnequalRightYHi yst out left right)
    lo := YulEvmCompiler.conv (pointAddUnequalRightYLo yst out left right) }

def pointAddUnequalNumeratorLimbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  limbsOfWords (pointAddUnequalNumeratorResult yst out left right)

def pointAddUnequalDenominatorLimbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  limbsOfWords (pointAddUnequalDenominatorResult yst out left right)

def pointAddUnequalInvLimbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  limbsOfWords (pointAddUnequalInvResult yst out left right)

def pointAddUnequalLambdaLimbs (yst : EvmState)
    (out left right : U256) : Fp.Limbs :=
  limbsOfWords (pointAddUnequalLambdaResult yst out left right)

private def toLawful (a : Fp.Limbs) : LawfulFp :=
  PrimeField.finEquiv (Fp.toField a)

private theorem numerator_result_eq_fpSubValue (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalNumeratorResult yst out left right =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
        (pointAddUnequalRightYHi yst out left right)
        (pointAddUnequalRightYLo yst out left right)
        (pointAddUnequalLeftYHi yst out left right)
        (pointAddUnequalLeftYLo yst out left right) := by
  simp only [pointAddUnequalNumeratorResult,
    pointAddUnequalNumeratorRepairValue,
    pointAddUnequalNumeratorRepaired,
    pointAddUnequalNumeratorRaw,
    pointAddUnequalNumeratorRawHi,
    pointAddUnequalNumeratorRawLo,
    pointAddUnequalNumeratorBorrow,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue,
    add_assoc]

private theorem numerator_eq (yst : EvmState) (out left right : U256) :
    pointAddUnequalNumeratorLimbs yst out left right =
      Fp.subSource (pointAddUnequalY2 yst out left right)
        (pointAddUnequalY1 yst out left right) := by
  rw [pointAddUnequalNumeratorLimbs, numerator_result_eq_fpSubValue]
  simpa only [limbsOfWords, pointAddUnequalY1, pointAddUnequalY2,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.convPair]
    using Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubValue
      (pointAddUnequalRightYHi yst out left right)
      (pointAddUnequalRightYLo yst out left right)
      (pointAddUnequalLeftYHi yst out left right)
      (pointAddUnequalLeftYLo yst out left right)

private theorem denominator_eq (yst : EvmState) (out left right : U256) :
    pointAddUnequalDenominatorLimbs yst out left right =
      Fp.subSource (pointAddUnequalRightXLimbs yst out left right)
        (pointAddUnequalLeftXLimbs yst out left right) := by
  rw [pointAddUnequalDenominatorLimbs,
    pointAddUnequalDenominatorResult_eq_fpSubValue]
  simpa only [limbsOfWords, pointAddUnequalLeftXLimbs,
    pointAddUnequalRightXLimbs,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.convPair]
    using Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubValue
      (pointAddUnequalRightXHi yst out left right)
      (pointAddUnequalRightXLo yst out left right)
      (pointAddUnequalLeftXHi yst out left right)
      (pointAddUnequalLeftXLo yst out left right)

private theorem inv_eq (yst : EvmState) (out left right : U256)
    (hx1 : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hx2 : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right)) :
    pointAddUnequalInvLimbs yst out left right =
      Fp.invCanonical (pointAddUnequalDenominatorLimbs yst out left right) := by
  apply Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutput_eq_invCanonical
  change Fp.Canonical (pointAddUnequalDenominatorLimbs yst out left right)
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

private theorem lambda_eq (yst : EvmState) (out left right : U256)
    (hx1 : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hy1 : Fp.Canonical (pointAddUnequalY1 yst out left right))
    (hx2 : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right))
    (hy2 : Fp.Canonical (pointAddUnequalY2 yst out left right)) :
    pointAddUnequalLambdaLimbs yst out left right =
      Fp.mulCanonical (pointAddUnequalNumeratorLimbs yst out left right)
        (pointAddUnequalInvLimbs yst out left right) := by
  apply fpMulOutput_eq_mulCanonical
  · change Fp.Canonical (pointAddUnequalNumeratorLimbs yst out left right)
    rw [numerator_eq]
    exact Fp.canonical_subSource hy2 hy1
  · change Fp.Canonical (pointAddUnequalInvLimbs yst out left right)
    rw [inv_eq yst out left right hx1 hx2, denominator_eq]
    exact Fp.canonical_invCanonical (Fp.canonical_subSource hx2 hx1)

theorem canonical_pointAddUnequalLambda (yst : EvmState)
    (out left right : U256)
    (hx1 : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hy1 : Fp.Canonical (pointAddUnequalY1 yst out left right))
    (hx2 : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right))
    (hy2 : Fp.Canonical (pointAddUnequalY2 yst out left right)) :
    Fp.Canonical (pointAddUnequalLambdaLimbs yst out left right) := by
  rw [lambda_eq yst out left right hx1 hy1 hx2 hy2]
  apply Fp.canonical_mulCanonical
  · rw [numerator_eq]
    exact Fp.canonical_subSource hy2 hy1
  · rw [inv_eq yst out left right hx1 hx2, denominator_eq]
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

theorem pointAddUnequalLambda_toLawful (yst : EvmState)
    (out left right : U256)
    (hx1 : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hy1 : Fp.Canonical (pointAddUnequalY1 yst out left right))
    (hx2 : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right))
    (hy2 : Fp.Canonical (pointAddUnequalY2 yst out left right))
    (_hne : toLawful (pointAddUnequalLeftXLimbs yst out left right) ≠
      toLawful (pointAddUnequalRightXLimbs yst out left right)) :
    toLawful (pointAddUnequalLambdaLimbs yst out left right) =
      (toLawful (pointAddUnequalY2 yst out left right) -
        toLawful (pointAddUnequalY1 yst out left right)) /
      (toLawful (pointAddUnequalRightXLimbs yst out left right) -
        toLawful (pointAddUnequalLeftXLimbs yst out left right)) := by
  have hnum := Fp.canonical_subSource hy2 hy1
  have hden := Fp.canonical_subSource hx2 hx1
  have hinv := Fp.canonical_invCanonical hden
  rw [lambda_eq yst out left right hx1 hy1 hx2 hy2,
    lawful_mulCanonical (by rw [numerator_eq]; exact hnum)
      (by rw [inv_eq yst out left right hx1 hx2, denominator_eq]; exact hinv),
    numerator_eq, lawful_subSource hy2 hy1,
    inv_eq yst out left right hx1 hx2,
    lawful_invCanonical (by rw [denominator_eq]; exact hden),
    denominator_eq, lawful_subSource hx2 hx1]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
