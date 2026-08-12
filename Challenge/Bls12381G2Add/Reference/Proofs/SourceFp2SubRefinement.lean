import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubExec
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

/-! # Arithmetic refinement of frozen G2ADD `fp2Sub` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

/-- Exact two-component result produced by the source helper, before making
any assumptions about pointer aliasing. -/
def fp2SubResult (yst : EvmState) (out a b : U256) :
    Challenge.Bls12381.ProofSupport.Fp2.Repr :=
  { c0 := fpWords (fp2SubC0 yst a b).1 (fp2SubC0 yst a b).2
    c1 := fpWords (fp2SubC1 yst out a b).1 (fp2SubC1 yst out a b).2 }

/-- Source-ordered left input.  Its second component is read after the first
component has been written, exactly as in the Yul helper. -/
def fp2SubScheduledA (yst : EvmState) (out a b : U256) :
    Challenge.Bls12381.ProofSupport.Fp2.Repr :=
  { c0 := (fp2At yst a).c0
    c1 := (fp2At (fp2SubAfterC0Stores yst out a b) a).c1 }

/-- Source-ordered right input, retaining the same alias-aware boundary. -/
def fp2SubScheduledB (yst : EvmState) (out a b : U256) :
    Challenge.Bls12381.ProofSupport.Fp2.Repr :=
  { c0 := (fp2At yst b).c0
    c1 := (fp2At (fp2SubAfterC0Stores yst out a b) b).c1 }

theorem fp2SubResult_eq_subSource (yst : EvmState) (out a b : U256) :
    fp2SubResult yst out a b =
      Challenge.Bls12381.ProofSupport.Fp2.subSource
        (fp2SubScheduledA yst out a b)
        (fp2SubScheduledB yst out a b) := by
  unfold fp2SubResult Challenge.Bls12381.ProofSupport.Fp2.subSource
    Challenge.Bls12381.ProofSupport.Fp2.mkRepr fp2SubScheduledA
    fp2SubScheduledB fp2SubC0 fp2SubC1 fpWords fp2At
  congr 1
  · exact conv_fpSubValue
      (loadWord yst.memory a.toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
      (loadWord yst.memory b.toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)
  · exact conv_fpSubValue
      (loadWord (fp2SubAfterC0Stores yst out a b).memory
        (a + BitVec.ofNat 256 64).toNat)
      (loadWord (fp2SubAfterC0Stores yst out a b).memory
        (a + BitVec.ofNat 256 96).toNat)
      (loadWord (fp2SubAfterC0Stores yst out a b).memory
        (b + BitVec.ofNat 256 64).toNat)
      (loadWord (fp2SubAfterC0Stores yst out a b).memory
        (b + BitVec.ofNat 256 96).toNat)

theorem fp2SubResult_canonical (yst : EvmState) (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2SubScheduledA yst out a b))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2SubScheduledB yst out a b)) :
    Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2SubResult yst out a b) := by
  rw [fp2SubResult_eq_subSource]
  exact Challenge.Bls12381.ProofSupport.Fp2.canonical_subSource ha hb

theorem fp2SubResult_toField (yst : EvmState) (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2SubScheduledA yst out a b))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2SubScheduledB yst out a b)) :
    Challenge.Bls12381.ProofSupport.Fp2.toField (fp2SubResult yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp2.toField
          (fp2SubScheduledA yst out a b) -
        Challenge.Bls12381.ProofSupport.Fp2.toField
          (fp2SubScheduledB yst out a b) := by
  rw [fp2SubResult_eq_subSource,
    Challenge.Bls12381.ProofSupport.Fp2.toField_subSource ha hb]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
