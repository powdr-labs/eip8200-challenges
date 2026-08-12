import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddExec
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

/-! # Arithmetic refinement of frozen G2ADD `fp2Add` -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

/-- Exact two-component result produced by the source helper, before making
any assumptions about pointer aliasing. -/
def fp2AddResult (yst : EvmState) (out a b : U256) :
    Challenge.Bls12381.ProofSupport.Fp2.Repr :=
  { c0 := fpWords (fp2AddC0 yst a b).1 (fp2AddC0 yst a b).2
    c1 := fpWords (fp2AddC1 yst out a b).1 (fp2AddC1 yst out a b).2 }

/-- Source-ordered left input.  Its second component is read after the first
component has been written, exactly as in the Yul helper. -/
def fp2AddScheduledA (yst : EvmState) (out a b : U256) :
    Challenge.Bls12381.ProofSupport.Fp2.Repr :=
  { c0 := (fp2At yst a).c0
    c1 := (fp2At (fp2AddAfterC0Stores yst out a b) a).c1 }

/-- Source-ordered right input, retaining the same alias-aware boundary. -/
def fp2AddScheduledB (yst : EvmState) (out a b : U256) :
    Challenge.Bls12381.ProofSupport.Fp2.Repr :=
  { c0 := (fp2At yst b).c0
    c1 := (fp2At (fp2AddAfterC0Stores yst out a b) b).c1 }

theorem fp2AddResult_eq_addSource (yst : EvmState) (out a b : U256) :
    fp2AddResult yst out a b =
      Challenge.Bls12381.ProofSupport.Fp2.addSource
        (fp2AddScheduledA yst out a b)
        (fp2AddScheduledB yst out a b) := by
  unfold fp2AddResult Challenge.Bls12381.ProofSupport.Fp2.addSource
    Challenge.Bls12381.ProofSupport.Fp2.mkRepr fp2AddScheduledA
    fp2AddScheduledB fp2AddC0 fp2AddC1 fpWords fp2At
  congr 1
  · exact conv_fpAddValue
      (loadWord yst.memory a.toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
      (loadWord yst.memory b.toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)
  · exact conv_fpAddValue
      (loadWord (fp2AddAfterC0Stores yst out a b).memory
        (a + BitVec.ofNat 256 64).toNat)
      (loadWord (fp2AddAfterC0Stores yst out a b).memory
        (a + BitVec.ofNat 256 96).toNat)
      (loadWord (fp2AddAfterC0Stores yst out a b).memory
        (b + BitVec.ofNat 256 64).toNat)
      (loadWord (fp2AddAfterC0Stores yst out a b).memory
        (b + BitVec.ofNat 256 96).toNat)

theorem fp2AddResult_canonical (yst : EvmState) (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2AddScheduledA yst out a b))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2AddScheduledB yst out a b)) :
    Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2AddResult yst out a b) := by
  rw [fp2AddResult_eq_addSource]
  exact Challenge.Bls12381.ProofSupport.Fp2.canonical_addSource ha hb

theorem fp2AddResult_toField (yst : EvmState) (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2AddScheduledA yst out a b))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical
      (fp2AddScheduledB yst out a b)) :
    Challenge.Bls12381.ProofSupport.Fp2.toField (fp2AddResult yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp2.toField
          (fp2AddScheduledA yst out a b) +
        Challenge.Bls12381.ProofSupport.Fp2.toField
          (fp2AddScheduledB yst out a b) := by
  rw [fp2AddResult_eq_addSource,
    Challenge.Bls12381.ProofSupport.Fp2.toField_addSource ha hb]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
