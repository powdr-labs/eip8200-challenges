import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2PredicatesExec
import Challenge.Bls12381.ProofSupport.Fp2Representation

set_option warningAsError true

/-! # Refinement of the frozen G2ADD Fp2 predicates -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

def fpWords (hi lo : U256) : Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }

/-- The frozen scalar validity word is one exactly below the BLS modulus. -/
theorem fpValidValue_eq_one_iff (hi lo : U256) :
    fpValidValue hi lo = 1 ↔
      Challenge.Bls12381.ProofSupport.Fp.value (fpWords hi lo) <
        EvmSemantics.Crypto.Bls12381.p := by
  have hconv := conv_fpValidValue hi lo
  have hcondition :
      Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        (fpWords hi lo) = Challenge.EvmProof.Limbs.wideGeWord
          (Challenge.Bls12381.ProofSupport.Fp.toWide (fpWords hi lo))
          Challenge.Bls12381.ProofSupport.Fp.modulusWide :=
    Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection_eq_wideGeWord _
  have hge :
      (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        (fpWords hi lo)).toNat ≠ 0 ↔
      EvmSemantics.Crypto.Bls12381.p ≤
        Challenge.Bls12381.ProofSupport.Fp.value (fpWords hi lo) := by
    rw [hcondition, Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff,
      Challenge.Bls12381.ProofSupport.Fp.toWide_value,
      Challenge.Bls12381.ProofSupport.Fp.modulusWide_value]
  have hnat := congrArg
    (fun value : EvmSemantics.UInt256 => value.toNat) hconv
  rw [Challenge.EvmProof.Word.word_toNat_isZero] at hnat
  constructor
  · intro hone
    have honeNat := congrArg BitVec.toNat hone
    have hzero :
        (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
          (fpWords hi lo)).toNat = 0 := by
      have hsource : (fpValidValue hi lo).toNat = 1 := by
        simpa using honeNat
      rw [← YulEvmCompiler.conv_toNat, hnat] at hsource
      split at hsource <;> rename_i hz
      · simpa [fpWords] using hz
      · omega
    by_contra hnot
    exact (hge.mpr (by omega)) hzero
  · intro hlt
    apply BitVec.toNat_injective
    have hzero :
        (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
          (fpWords hi lo)).toNat = 0 := by
      by_contra hne
      exact (not_lt_of_ge (hge.mp hne)) hlt
    change (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }).toNat =
        0 at hzero
    rw [← YulEvmCompiler.conv_toNat, hnat, hzero]
    rfl

theorem fpValidValue_eq_one_iff_canonical (hi lo : U256) :
    fpValidValue hi lo = 1 ↔
      Challenge.Bls12381.ProofSupport.Fp.Canonical (fpWords hi lo) := by
  rw [fpValidValue_eq_one_iff]
  constructor
  · exact Challenge.Bls12381.ProofSupport.Fp.canonical_of_value_lt _
  · exact fun h => h.2

private theorem fpValidValue_zero_or_one (hi lo : U256) :
    fpValidValue hi lo = 0 ∨ fpValidValue hi lo = 1 := by
  simp only [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpValidValue,
    b2w]
  split <;> simp

private theorem fpZeroValue_eq_one_iff (hi lo : U256) :
    fpZeroValue hi lo = 1 ↔ hi = 0 ∧ lo = 0 := by
  simp only [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue,
    b2w]
  split <;> split <;> simp_all

private theorem fpZeroValue_cases (hi lo : U256) :
    fpZeroValue hi lo = 0 ∨ fpZeroValue hi lo = 1 := by
  simp only [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue,
    b2w]
  split <;> split <;> decide

private theorem fpEqValue_eq_one_iff (ahi alo bhi blo : U256) :
    fpEqValue ahi alo bhi blo = 1 ↔ ahi = bhi ∧ alo = blo := by
  simp only [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpEqValue,
    b2w]
  split <;> split <;> simp_all

private theorem fpEqValue_cases (ahi alo bhi blo : U256) :
    fpEqValue ahi alo bhi blo = 0 ∨ fpEqValue ahi alo bhi blo = 1 := by
  simp only [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpEqValue,
    b2w]
  split <;> split <;> decide

private theorem land_eq_one_iff_of_zero_or_one {a b : U256}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem fp2ValidValue_eq_one_iff_canonical (yst : EvmState) (ptr : U256) :
    fp2ValidValue yst ptr = 1 ↔
      Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst ptr) := by
  let hi0 := loadWord yst.memory ptr.toNat
  let lo0 := loadWord yst.memory (ptr + BitVec.ofNat 256 32).toNat
  let hi1 := loadWord yst.memory (ptr + BitVec.ofNat 256 64).toNat
  let lo1 := loadWord yst.memory (ptr + BitVec.ofNat 256 96).toNat
  have hland := land_eq_one_iff_of_zero_or_one
    (fpValidValue_zero_or_one hi0 lo0)
    (fpValidValue_zero_or_one hi1 lo1)
  change fpValidValue hi0 lo0 &&& fpValidValue hi1 lo1 = 1 ↔ _
  rw [hland, fpValidValue_eq_one_iff_canonical,
    fpValidValue_eq_one_iff_canonical,
    Challenge.Bls12381.ProofSupport.Fp2.canonical_iff]
  rfl

/-- Compact source-word view used by validation and point branches. -/
structure Fp2Words where
  c0Hi : U256
  c0Lo : U256
  c1Hi : U256
  c1Lo : U256
deriving DecidableEq

def fp2WordsAt (yst : EvmState) (ptr : U256) : Fp2Words :=
  { c0Hi := loadWord yst.memory ptr.toNat
    c0Lo := loadWord yst.memory (ptr + BitVec.ofNat 256 32).toNat
    c1Hi := loadWord yst.memory (ptr + BitVec.ofNat 256 64).toNat
    c1Lo := loadWord yst.memory (ptr + BitVec.ofNat 256 96).toNat }

/-- Two Fp2 memory views are equal when their four selected words are equal.
Keeping this representation lemma below the arithmetic helpers prevents frame
proofs from importing the complete `onCurve` development. -/
theorem fp2At_eq_of_loads (left right : EvmState) (ptr : U256)
    (h0 : loadWord left.memory ptr.toNat = loadWord right.memory ptr.toNat)
    (h1 : loadWord left.memory (ptr + BitVec.ofNat 256 32).toNat =
      loadWord right.memory (ptr + BitVec.ofNat 256 32).toNat)
    (h2 : loadWord left.memory (ptr + BitVec.ofNat 256 64).toNat =
      loadWord right.memory (ptr + BitVec.ofNat 256 64).toNat)
    (h3 : loadWord left.memory (ptr + BitVec.ofNat 256 96).toNat =
      loadWord right.memory (ptr + BitVec.ofNat 256 96).toNat) :
    fp2At left ptr = fp2At right ptr := by
  unfold fp2At
  rw [h0, h1, h2, h3]

def fp2ZeroWords : Fp2Words := ⟨0, 0, 0, 0⟩

def fp2ZeroWordsValue (words : Fp2Words) : U256 :=
  fpZeroValue words.c0Hi words.c0Lo &&&
    fpZeroValue words.c1Hi words.c1Lo

theorem fp2ZeroValue_eq_words (yst : EvmState) (ptr : U256) :
    fp2ZeroValue yst ptr = fp2ZeroWordsValue (fp2WordsAt yst ptr) := by
  rfl

theorem fp2ZeroWordsValue_eq_one_iff (words : Fp2Words) :
    fp2ZeroWordsValue words = 1 ↔ words = fp2ZeroWords := by
  have hland := land_eq_one_iff_of_zero_or_one
    (fpZeroValue_cases words.c0Hi words.c0Lo)
    (fpZeroValue_cases words.c1Hi words.c1Lo)
  rw [fp2ZeroWordsValue, hland, fpZeroValue_eq_one_iff,
    fpZeroValue_eq_one_iff]
  cases words
  simp only [fp2ZeroWords, Fp2Words.mk.injEq]
  tauto

theorem fp2ZeroValue_eq_one_iff_words (yst : EvmState) (ptr : U256) :
    fp2ZeroValue yst ptr = 1 ↔
      fp2WordsAt yst ptr = fp2ZeroWords := by
  rw [fp2ZeroValue_eq_words, fp2ZeroWordsValue_eq_one_iff]

def fp2EqWordsValue (a b : Fp2Words) : U256 :=
  fpEqValue a.c0Hi a.c0Lo b.c0Hi b.c0Lo &&&
    fpEqValue a.c1Hi a.c1Lo b.c1Hi b.c1Lo

theorem fp2EqValue_eq_words (yst : EvmState) (a b : U256) :
    fp2EqValue yst a b =
      fp2EqWordsValue (fp2WordsAt yst a) (fp2WordsAt yst b) := by
  rfl

theorem fp2EqWordsValue_eq_one_iff (a b : Fp2Words) :
    fp2EqWordsValue a b = 1 ↔ a = b := by
  have hland := land_eq_one_iff_of_zero_or_one
    (fpEqValue_cases a.c0Hi a.c0Lo b.c0Hi b.c0Lo)
    (fpEqValue_cases a.c1Hi a.c1Lo b.c1Hi b.c1Lo)
  rw [fp2EqWordsValue, hland, fpEqValue_eq_one_iff,
    fpEqValue_eq_one_iff]
  cases a
  cases b
  simp only [Fp2Words.mk.injEq]
  tauto

theorem fp2EqValue_eq_one_iff_words (yst : EvmState) (a b : U256) :
    fp2EqValue yst a b = 1 ↔
      fp2WordsAt yst a = fp2WordsAt yst b := by
  rw [fp2EqValue_eq_words, fp2EqWordsValue_eq_one_iff]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
