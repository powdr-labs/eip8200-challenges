import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFinitePostExec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleLawful
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteUnequalLawful
import Challenge.Bls12381.ProofSupport.CodecRepresentation

set_option warningAsError true

/-! # G1ADD common post-slope lawful refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev LawfulFp := PrimeField.LawfulFp

private def limbsOfWords (words : U256 × U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv words.1, lo := YulEvmCompiler.conv words.2 }

def mainFinitePostX1 (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainDecodedWord yst 0, mainDecodedWord yst 32)

def mainFinitePostY1 (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainDecodedWord yst 64, mainDecodedWord yst 96)

def mainFinitePostX2 (yst : EvmState) : Fp.Limbs :=
  limbsOfWords (mainDecodedWord yst 128, mainDecodedWord yst 160)

def mainFinitePostLambda (lam : U256 × U256) : Fp.Limbs :=
  limbsOfWords lam

def mainFinitePostLambdaSq (st : EvmState) (lam : U256 × U256) : Fp.Limbs :=
  fpMulOutputLimbs st lam.1 lam.2 lam.1 lam.2

def mainFinitePostX3First (yst st : EvmState) (lam : U256 × U256) :
    Fp.Limbs := limbsOfWords (mainFinitePostX3FirstWords yst st lam)

def mainFinitePostX3 (yst st : EvmState) (lam : U256 × U256) : Fp.Limbs :=
  limbsOfWords (mainFinitePostX3Words yst st lam)

def mainFinitePostDelta (yst st : EvmState) (lam : U256 × U256) : Fp.Limbs :=
  limbsOfWords (mainFinitePostDeltaWords yst st lam)

def mainFinitePostYProduct (yst st : EvmState) (lam : U256 × U256) :
    Fp.Limbs :=
  fpMulOutputLimbs (mainFinitePostDeltaArgsState yst st lam)
    lam.1 lam.2 (mainFinitePostDeltaWords yst st lam).1
    (mainFinitePostDeltaWords yst st lam).2

def mainFinitePostY3 (yst st : EvmState) (lam : U256 × U256) : Fp.Limbs :=
  limbsOfWords (mainFinitePostY3Words yst st lam)

private def toLawful (a : Fp.Limbs) : LawfulFp :=
  PrimeField.finEquiv (Fp.toField a)

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

private theorem lambdaSq_eq (st : EvmState) (lam : U256 × U256)
    (hlam : Fp.Canonical (mainFinitePostLambda lam)) :
    mainFinitePostLambdaSq st lam =
      Fp.mulCanonical (mainFinitePostLambda lam)
        (mainFinitePostLambda lam) := by
  exact fpMulOutput_eq_mulCanonical _ _ _ _ _ hlam hlam

private theorem x3First_eq (yst st : EvmState) (lam : U256 × U256) :
    mainFinitePostX3First yst st lam =
      Fp.subSource (mainFinitePostLambdaSq st lam)
        (mainFinitePostX1 yst) :=
  conv_fpSubValue _ _ _ _

private theorem x3_eq (yst st : EvmState) (lam : U256 × U256) :
    mainFinitePostX3 yst st lam =
      Fp.subSource (mainFinitePostX3First yst st lam)
        (mainFinitePostX2 yst) :=
  conv_fpSubValue _ _ _ _

private theorem delta_eq (yst st : EvmState) (lam : U256 × U256) :
    mainFinitePostDelta yst st lam =
      Fp.subSource (mainFinitePostX1 yst)
        (mainFinitePostX3 yst st lam) :=
  conv_fpSubValue _ _ _ _

private theorem yProduct_eq (yst st : EvmState) (lam : U256 × U256)
    (hlam : Fp.Canonical (mainFinitePostLambda lam))
    (hdelta : Fp.Canonical (mainFinitePostDelta yst st lam)) :
    mainFinitePostYProduct yst st lam =
      Fp.mulCanonical (mainFinitePostLambda lam)
        (mainFinitePostDelta yst st lam) := by
  exact fpMulOutput_eq_mulCanonical _ _ _ _ _ hlam hdelta

private theorem y3_eq (yst st : EvmState) (lam : U256 × U256) :
    mainFinitePostY3 yst st lam =
      Fp.subSource (mainFinitePostYProduct yst st lam)
        (mainFinitePostY1 yst) :=
  conv_fpSubValue _ _ _ _

private theorem lawful_mulCanonical {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    toLawful (Fp.mulCanonical a b) = toLawful a * toLawful b := by
  have h := congrArg PrimeField.finEquiv (Fp.toField_mulCanonical ha hb)
  simpa only [toLawful, map_mul] using h

private theorem lawful_subSource {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    toLawful (Fp.subSource a b) = toLawful a - toLawful b := by
  have h := congrArg PrimeField.finEquiv (Fp.toField_subSource ha hb)
  simpa only [toLawful, map_sub] using h

/-- The common source path produces canonical output coordinates. -/
theorem canonical_mainFinitePostCoordinates (yst st : EvmState)
    (lam : U256 × U256)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical (mainFinitePostLambda lam)) :
    Fp.Canonical (mainFinitePostX3 yst st lam) ∧
      Fp.Canonical (mainFinitePostY3 yst st lam) := by
  have hsq : Fp.Canonical (mainFinitePostLambdaSq st lam) := by
    rw [lambdaSq_eq st lam hlam]
    exact Fp.canonical_mulCanonical hlam hlam
  have hfirst : Fp.Canonical (mainFinitePostX3First yst st lam) := by
    rw [x3First_eq]
    exact Fp.canonical_subSource hsq hx1
  have hx3 : Fp.Canonical (mainFinitePostX3 yst st lam) := by
    rw [x3_eq]
    exact Fp.canonical_subSource hfirst hx2
  have hdelta : Fp.Canonical (mainFinitePostDelta yst st lam) := by
    rw [delta_eq]
    exact Fp.canonical_subSource hx1 hx3
  have hproduct : Fp.Canonical (mainFinitePostYProduct yst st lam) := by
    rw [yProduct_eq yst st lam hlam hdelta]
    exact Fp.canonical_mulCanonical hlam hdelta
  refine ⟨hx3, ?_⟩
  rw [y3_eq]
  exact Fp.canonical_subSource hproduct hy1

/-- The exact source output coordinates implement the common affine formulas
from an already-established lawful slope. -/
theorem mainFinitePostCoordinates_toLawful (yst st : EvmState)
    (lam : U256 × U256)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical (mainFinitePostLambda lam)) :
    toLawful (mainFinitePostX3 yst st lam) =
        toLawful (mainFinitePostLambda lam) ^ 2 -
          toLawful (mainFinitePostX1 yst) -
          toLawful (mainFinitePostX2 yst) ∧
      toLawful (mainFinitePostY3 yst st lam) =
        toLawful (mainFinitePostLambda lam) *
          (toLawful (mainFinitePostX1 yst) -
            toLawful (mainFinitePostX3 yst st lam)) -
          toLawful (mainFinitePostY1 yst) := by
  have hcanon := canonical_mainFinitePostCoordinates yst st lam
    hx1 hy1 hx2 hlam
  have hsq : Fp.Canonical (mainFinitePostLambdaSq st lam) := by
    rw [lambdaSq_eq st lam hlam]
    exact Fp.canonical_mulCanonical hlam hlam
  have hfirst : Fp.Canonical (mainFinitePostX3First yst st lam) := by
    rw [x3First_eq]
    exact Fp.canonical_subSource hsq hx1
  have hdelta : Fp.Canonical (mainFinitePostDelta yst st lam) := by
    rw [delta_eq]
    exact Fp.canonical_subSource hx1 hcanon.1
  have hproduct : Fp.Canonical (mainFinitePostYProduct yst st lam) := by
    rw [yProduct_eq yst st lam hlam hdelta]
    exact Fp.canonical_mulCanonical hlam hdelta
  constructor
  · rw [x3_eq, lawful_subSource hfirst hx2, x3First_eq,
      lawful_subSource hsq hx1, lambdaSq_eq st lam hlam,
      lawful_mulCanonical hlam hlam]
    ring
  · rw [y3_eq, lawful_subSource hproduct hy1,
      yProduct_eq yst st lam hlam hdelta,
      lawful_mulCanonical hlam hdelta, delta_eq,
      lawful_subSource hx1 hcanon.1]

/-- The lawful affine point represented by the two canonical source output
coordinates. -/
def mainFinitePostPoint (yst st : EvmState) (lam : U256 × U256) :
    G1Affine.Point :=
  .affine (toLawful (mainFinitePostX3 yst st lam))
    (toLawful (mainFinitePostY3 yst st lam))

/-- Given the already-proved unequal-x slope, the common source tail is
exactly lawful affine addition. -/
theorem mainFinitePostPoint_eq_add_of_x_ne (yst st : EvmState)
    (lam : U256 × U256)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical (mainFinitePostLambda lam))
    (hxne : toLawful (mainFinitePostX1 yst) ≠
      toLawful (mainFinitePostX2 yst))
    (hslope : toLawful (mainFinitePostLambda lam) =
      (toLawful (mainFiniteUnequalY2 yst) -
        toLawful (mainFinitePostY1 yst)) /
      (toLawful (mainFinitePostX2 yst) -
        toLawful (mainFinitePostX1 yst))) :
    mainFinitePostPoint yst st lam =
      G1Affine.add
        (.affine (toLawful (mainFinitePostX1 yst))
          (toLawful (mainFinitePostY1 yst)))
        (.affine (toLawful (mainFinitePostX2 yst))
          (toLawful (mainFiniteUnequalY2 yst))) := by
  have hcoords := mainFinitePostCoordinates_toLawful yst st lam
    hx1 hy1 hx2 hlam
  rw [G1Affine.add, LawfulAffine.add_of_x_ne _ _ _ _ _ hxne]
  simp only [mainFinitePostPoint]
  rw [hcoords.2, hcoords.1, hslope]

/-- Given the already-proved doubling slope and equal x-coordinate, the
common source tail is exactly lawful affine doubling. -/
theorem mainFinitePostPoint_eq_double (yst st : EvmState)
    (lam : U256 × U256)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical (mainFinitePostLambda lam))
    (hyne : toLawful (mainFinitePostY1 yst) ≠ 0)
    (hxEq : toLawful (mainFinitePostX2 yst) =
      toLawful (mainFinitePostX1 yst))
    (hslope : toLawful (mainFinitePostLambda lam) =
      (3 * toLawful (mainFinitePostX1 yst) ^ 2) /
        (2 * toLawful (mainFinitePostY1 yst))) :
    mainFinitePostPoint yst st lam =
      G1Affine.double
        (.affine (toLawful (mainFinitePostX1 yst))
          (toLawful (mainFinitePostY1 yst))) := by
  have hcoords := mainFinitePostCoordinates_toLawful yst st lam
    hx1 hy1 hx2 hlam
  simp only [mainFinitePostPoint, G1Affine.double, LawfulAffine.double,
    hyne, ↓reduceIte, G1Affine.curve]
  rw [hcoords.2, hcoords.1, hslope, hxEq]
  ring

private def wordBytes (value : Nat) : List UInt8 :=
  (EvmSemantics.Data.Bytes.natToBytesPadded value 32).toList

private theorem wordBytes_length (value : Nat) :
    (wordBytes value).length = 32 := by
  simpa [wordBytes, YulEvmCompiler.ByteArray.toList_eq_data,
    Array.length_toList] using
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size value 32

private theorem bytesNat_wordBytes (value : Nat) (hvalue : value < 2 ^ 256) :
    Challenge.EvmProof.Bytes.bytesNat (wordBytes value) = value := by
  change EvmSemantics.Data.Bytes.bytesToBigEndianNat
    (EvmSemantics.Data.Bytes.natToBytesPadded value 32) = value
  apply Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
  simpa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] using hvalue

private theorem readBytes_storeWord_eq_wordBytes
    (memory : Nat → UInt8) (start : Nat) (word : U256) :
    readBytes (storeWord memory start word) start 32 =
      wordBytes word.toNat := by
  apply Challenge.EvmProof.Bytes.bytesNat_injective_of_length
  · simp [readBytes, wordBytes_length]
  · rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord,
      bytesNat_wordBytes word.toNat word.isLt]

private theorem wordBytes_pair_eq_encodeFp {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    wordBytes a.hi.toNat ++ wordBytes a.lo.toNat =
      (Codec.encodeFp (Fp.toField a)).toList := by
  apply Challenge.EvmProof.Bytes.bytesNat_injective_of_length
  · rw [List.length_append, wordBytes_length, wordBytes_length,
      YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
    simp [Codec.fpBytes, Codec.encodeFp_size]
  · rw [Challenge.EvmProof.Bytes.bytesNat_append,
      bytesNat_wordBytes a.hi.toNat a.hi.val.isLt,
      bytesNat_wordBytes a.lo.toNat a.lo.val.isLt, wordBytes_length,
      Challenge.EvmProof.Bytes.bytesNat_toList]
    have hencode := Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
      (Fp.toField a).val 64 (by
        exact (Fp.toField a).isLt.trans (by
          norm_num [EvmSemantics.Crypto.Bls12381.p,
            EvmSemantics.Crypto.Bls12381.absU]))
    rw [show Codec.encodeFp (Fp.toField a) =
      EvmSemantics.Data.Bytes.natToBytesPadded (Fp.toField a).val 64 by rfl,
      hencode]
    rw [show (256 : Nat) ^ 32 = Challenge.EvmProof.Limbs.radix by
      norm_num [Challenge.EvmProof.Limbs.radix, ← pow_mul]]
    rw [show (Fp.toField a).val = Fp.value a by
      simp [Fp.toField, Nat.mod_eq_of_lt ha.2]]
    simp only [Fp.value]
    rw [Nat.mul_comm, Nat.add_comm]

private theorem mainFinitePostStoredState_readOutput (yst st : EvmState)
    (lam : U256 × U256) :
    readBytes (mainFinitePostStoredState yst st lam).memory 0 128 =
      wordBytes (mainFinitePostX3Words yst st lam).1.toNat ++
      wordBytes (mainFinitePostX3Words yst st lam).2.toNat ++
      wordBytes (mainFinitePostY3Words yst st lam).1.toNat ++
      wordBytes (mainFinitePostY3Words yst st lam).2.toNat := by
  simp only [mainFinitePostStoredState, mainStorePointState]
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 32 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 64 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes]
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 96 _ (by omega)]
  rw [readBytes_storeWord_eq_wordBytes, readBytes_storeWord_eq_wordBytes]
  simp only [List.append_assoc]

/-- The exact `storePoint; return(0,128)` tail returns the canonical EIP G1
encoding of its two canonical result limbs. -/
theorem mainFinitePost_returned_codec (yst st : EvmState)
    (lam : U256 × U256)
    (hx1 : Fp.Canonical (mainFinitePostX1 yst))
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hx2 : Fp.Canonical (mainFinitePostX2 yst))
    (hlam : Fp.Canonical (mainFinitePostLambda lam)) :
    (mainFinitePostReturnState yst st lam).halted =
      some (HaltKind.ret,
        (Codec.encodeG1 (G1Affine.toWire
          (mainFinitePostPoint yst st lam))).toList) := by
  have hcanon := canonical_mainFinitePostCoordinates yst st lam
    hx1 hy1 hx2 hlam
  change some (HaltKind.ret,
    readBytes (mainFinitePostStoredState yst st lam).memory 0 128) = _
  rw [mainFinitePostStoredState_readOutput]
  simp only [mainFinitePostPoint, G1Affine.toWire,
    Codec.encodeG1, EvmSemantics.Crypto.Bls12381G1Add.encodePoint,
    YulEvmCompiler.ByteArray.toList_eq_data, ByteArray.data_append,
    Array.toList_append]
  rw [show PrimeField.finEquiv.symm
      (toLawful (mainFinitePostX3 yst st lam)) =
      Fp.toField (mainFinitePostX3 yst st lam) by
        change PrimeField.finEquiv.symm
          (PrimeField.finEquiv (Fp.toField (mainFinitePostX3 yst st lam))) = _
        exact PrimeField.finEquiv.symm_apply_apply _,
    show PrimeField.finEquiv.symm
      (toLawful (mainFinitePostY3 yst st lam)) =
      Fp.toField (mainFinitePostY3 yst st lam) by
        change PrimeField.finEquiv.symm
          (PrimeField.finEquiv (Fp.toField (mainFinitePostY3 yst st lam))) = _
        exact PrimeField.finEquiv.symm_apply_apply _]
  have hxbytes := wordBytes_pair_eq_encodeFp hcanon.1
  have hybytes := wordBytes_pair_eq_encodeFp hcanon.2
  rw [YulEvmCompiler.ByteArray.toList_eq_data] at hxbytes hybytes
  have hxbytes' :
      wordBytes (mainFinitePostX3Words yst st lam).1.toNat ++
        wordBytes (mainFinitePostX3Words yst st lam).2.toNat =
      (Codec.encodeFp (Fp.toField
        (mainFinitePostX3 yst st lam))).data.toList := by
    simpa [mainFinitePostX3, limbsOfWords,
      YulEvmCompiler.conv_toNat] using hxbytes
  have hybytes' :
      wordBytes (mainFinitePostY3Words yst st lam).1.toNat ++
        wordBytes (mainFinitePostY3Words yst st lam).2.toNat =
      (Codec.encodeFp (Fp.toField
        (mainFinitePostY3 yst st lam))).data.toList := by
    simpa [mainFinitePostY3, limbsOfWords,
      YulEvmCompiler.conv_toNat] using hybytes
  congr 2
  calc
    wordBytes (mainFinitePostX3Words yst st lam).1.toNat ++
          wordBytes (mainFinitePostX3Words yst st lam).2.toNat ++
        wordBytes (mainFinitePostY3Words yst st lam).1.toNat ++
      wordBytes (mainFinitePostY3Words yst st lam).2.toNat =
        (wordBytes (mainFinitePostX3Words yst st lam).1.toNat ++
          wordBytes (mainFinitePostX3Words yst st lam).2.toNat) ++
        (wordBytes (mainFinitePostY3Words yst st lam).1.toNat ++
          wordBytes (mainFinitePostY3Words yst st lam).2.toNat) := by
            rw [List.append_assoc]
    _ = _ := congrArg₂ (· ++ ·) hxbytes' hybytes'

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
