import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvExec
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true
/-! # Arithmetic phase bridges for frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics.EVM

theorem fp2InvSquare0_eq_mulCanonical (yst : EvmState) (a : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpWords (loadWord yst.memory a.toNat)
        (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat))) :
    pairWords (fp2InvSquare0 yst a) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fpWords (loadWord yst.memory a.toNat)
          (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat))
        (fpWords (loadWord yst.memory a.toNat)
          (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)) := by
  exact fpMulOutput_eq_mulCanonical (fp2InvAfterSquare0Reads yst a)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat) ha ha

def fp2InvSquare1Input (yst : EvmState) (a : U256) :=
  let s := fp2InvAfterSquare0Stores yst a
  fpWords (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)

theorem fp2InvSquare1_eq_mulCanonical (yst : EvmState) (a : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fp2InvSquare1Input yst a)) :
    pairWords (fp2InvSquare1 yst a) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fp2InvSquare1Input yst a) (fp2InvSquare1Input yst a) := by
  exact fpMulOutput_eq_mulCanonical (fp2InvAfterSquare1Reads yst a)
    (loadWord (fp2InvAfterSquare0Stores yst a).memory
      (a + BitVec.ofNat 256 64).toNat)
    (loadWord (fp2InvAfterSquare0Stores yst a).memory
      (a + BitVec.ofNat 256 96).toNat)
    (loadWord (fp2InvAfterSquare0Stores yst a).memory
      (a + BitVec.ofNat 256 64).toNat)
    (loadWord (fp2InvAfterSquare0Stores yst a).memory
      (a + BitVec.ofNat 256 96).toNat) ha ha

theorem fp2InvNorm_eq_addSource (yst : EvmState) (a : U256) :
    pairWords (fp2InvNorm yst a) =
      Challenge.Bls12381.ProofSupport.Fp.addSource
        (fpWords (loadWord (fp2InvAfterSquare1Stores yst a).memory 1536)
          (loadWord (fp2InvAfterSquare1Stores yst a).memory 1568))
        (fpWords (loadWord (fp2InvAfterSquare1Stores yst a).memory 1600)
          (loadWord (fp2InvAfterSquare1Stores yst a).memory 1632)) := by
  exact conv_fpAddValue _ _ _ _

theorem fp2InvScalar_eq_invCanonical (yst : EvmState) (a : U256)
    (hnorm : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (pairWords (fp2InvNorm yst a))) :
    pairWords (fp2InvScalar yst a) =
      Challenge.Bls12381.ProofSupport.Fp.invCanonical
        (pairWords (fp2InvNorm yst a)) := by
  exact fpInvOutput_eq_invCanonical (fp2InvAfterNormReads yst a)
    (fp2InvNorm yst a).1 (fp2InvNorm yst a).2 hnorm

def fp2InvRealLeft (yst : EvmState) (a : U256) :=
  let s := fp2InvAfterScalarStores yst a
  fpWords (loadWord s.memory a.toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 32).toNat)
def fp2InvScalarStored (yst : EvmState) (a : U256) :=
  let s := fp2InvAfterScalarStores yst a
  fpWords (loadWord s.memory 1664) (loadWord s.memory 1696)

theorem fp2InvReal_eq_mulCanonical (yst : EvmState) (a : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fp2InvRealLeft yst a))
    (hs : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fp2InvScalarStored yst a)) :
    pairWords (fp2InvReal yst a) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fp2InvRealLeft yst a) (fp2InvScalarStored yst a) := by
  exact fpMulOutput_eq_mulCanonical (fp2InvAfterRealReads yst a)
    (loadWord (fp2InvAfterScalarStores yst a).memory a.toNat)
    (loadWord (fp2InvAfterScalarStores yst a).memory
      (a + BitVec.ofNat 256 32).toNat)
    (loadWord (fp2InvAfterScalarStores yst a).memory 1664)
    (loadWord (fp2InvAfterScalarStores yst a).memory 1696) ha hs

theorem fp2InvNeg_eq_subSourceZero (yst : EvmState) (out a : U256) :
    pairWords (fp2InvNeg yst out a) =
      Challenge.Bls12381.ProofSupport.Fp.subSource (fpWords 0 0)
        (fpWords
          (loadWord (fp2InvAfterRealStores yst out a).memory
            (a + BitVec.ofNat 256 64).toNat)
          (loadWord (fp2InvAfterRealStores yst out a).memory
            (a + BitVec.ofNat 256 96).toNat)) := by
  exact conv_fpSubValue _ _ _ _

def fp2InvImagScalar (yst : EvmState) (out a : U256) :=
  fpWords (loadWord (fp2InvAfterNegReads yst out a).memory 1664)
    (loadWord (fp2InvAfterNegReads yst out a).memory 1696)

theorem fp2InvImag_eq_mulCanonical (yst : EvmState) (out a : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (pairWords (fp2InvNeg yst out a)))
    (hs : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fp2InvImagScalar yst out a)) :
    pairWords (fp2InvImag yst out a) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (pairWords (fp2InvNeg yst out a)) (fp2InvImagScalar yst out a) := by
  exact fpMulOutput_eq_mulCanonical (fp2InvAfterImagReads yst out a)
    (fp2InvNeg yst out a).1 (fp2InvNeg yst out a).2
    (loadWord (fp2InvAfterNegReads yst out a).memory 1664)
    (loadWord (fp2InvAfterNegReads yst out a).memory 1696) ha hs

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
