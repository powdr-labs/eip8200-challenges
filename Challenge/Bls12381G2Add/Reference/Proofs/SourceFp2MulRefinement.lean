import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulExec
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true
/-! # Arithmetic phase bridges for frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics.EVM

def pairWords (z : U256 × U256) : Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  fpWords z.1 z.2

def fp2MulV0Left (yst : EvmState) (a : U256) :=
  fpWords (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
def fp2MulV0Right (yst : EvmState) (b : U256) :=
  fpWords (loadWord yst.memory b.toNat)
    (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)

theorem fp2MulV0_eq_mulCanonical (yst : EvmState) (a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical (fp2MulV0Left yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical (fp2MulV0Right yst b)) :
    pairWords (fp2MulV0 yst a b) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fp2MulV0Left yst a) (fp2MulV0Right yst b) := by
  exact fpMulOutput_eq_mulCanonical (fp2MulAfterV0Reads yst a b)
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory b.toNat)
    (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat) ha hb

def fp2MulV1Left (yst : EvmState) (a b : U256) :=
  let s := fp2MulAfterV0Stores yst a b
  fpWords (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)
def fp2MulV1Right (yst : EvmState) (a b : U256) :=
  let s := fp2MulAfterV0Stores yst a b
  fpWords (loadWord s.memory (b + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 96).toNat)

theorem fp2MulV1_eq_mulCanonical (yst : EvmState) (a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical (fp2MulV1Left yst a b))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical (fp2MulV1Right yst a b)) :
    pairWords (fp2MulV1 yst a b) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fp2MulV1Left yst a b) (fp2MulV1Right yst a b) := by
  exact fpMulOutput_eq_mulCanonical (fp2MulAfterV1Reads yst a b)
    (loadWord (fp2MulAfterV0Stores yst a b).memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord (fp2MulAfterV0Stores yst a b).memory (a + BitVec.ofNat 256 96).toNat)
    (loadWord (fp2MulAfterV0Stores yst a b).memory (b + BitVec.ofNat 256 64).toNat)
    (loadWord (fp2MulAfterV0Stores yst a b).memory (b + BitVec.ofNat 256 96).toNat) ha hb

theorem fp2MulReal_eq_subSource (yst : EvmState) (a b : U256) :
    pairWords (fp2MulReal yst a b) =
      Challenge.Bls12381.ProofSupport.Fp.subSource
        (fpWords (loadWord (fp2MulAfterV1Stores yst a b).memory 1536)
          (loadWord (fp2MulAfterV1Stores yst a b).memory 1568))
        (fpWords (loadWord (fp2MulAfterV1Stores yst a b).memory 1600)
          (loadWord (fp2MulAfterV1Stores yst a b).memory 1632)) := by
  exact conv_fpSubValue _ _ _ _

theorem fp2MulSumA_eq_addSource (yst : EvmState) (out a b : U256) :
    pairWords (fp2MulSumA yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp.addSource
        (fp2At (fp2MulAfterRealStores yst out a b) a).c0
        (fp2At (fp2MulAfterRealStores yst out a b) a).c1 := by
  exact conv_fpAddValue _ _ _ _

theorem fp2MulSumB_eq_addSource (yst : EvmState) (out a b : U256) :
    pairWords (fp2MulSumB yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp.addSource
        (fp2At (fp2MulAfterSumAStores yst out a b) b).c0
        (fp2At (fp2MulAfterSumAStores yst out a b) b).c1 := by
  exact conv_fpAddValue _ _ _ _

def fp2MulCrossLeft (yst : EvmState) (out a b : U256) :=
  let s := fp2MulAfterSumBStores yst out a b
  fpWords (loadWord s.memory 1664) (loadWord s.memory 1696)
def fp2MulCrossRight (yst : EvmState) (out a b : U256) :=
  let s := fp2MulAfterSumBStores yst out a b
  fpWords (loadWord s.memory 1728) (loadWord s.memory 1760)

theorem fp2MulCross_eq_mulCanonical (yst : EvmState) (out a b : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fp2MulCrossLeft yst out a b))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fp2MulCrossRight yst out a b)) :
    pairWords (fp2MulCross yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fp2MulCrossLeft yst out a b) (fp2MulCrossRight yst out a b) := by
  exact fpMulOutput_eq_mulCanonical (fp2MulAfterCrossReads yst out a b)
    (loadWord (fp2MulAfterSumBStores yst out a b).memory 1664)
    (loadWord (fp2MulAfterSumBStores yst out a b).memory 1696)
    (loadWord (fp2MulAfterSumBStores yst out a b).memory 1728)
    (loadWord (fp2MulAfterSumBStores yst out a b).memory 1760) ha hb

theorem fp2MulVSum_eq_addSource (yst : EvmState) (out a b : U256) :
    pairWords (fp2MulVSum yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp.addSource
        (fpWords (loadWord (fp2MulAfterCrossStores yst out a b).memory 1536)
          (loadWord (fp2MulAfterCrossStores yst out a b).memory 1568))
        (fpWords (loadWord (fp2MulAfterCrossStores yst out a b).memory 1600)
          (loadWord (fp2MulAfterCrossStores yst out a b).memory 1632)) := by
  exact conv_fpAddValue _ _ _ _

theorem fp2MulImag_eq_subSource (yst : EvmState) (out a b : U256) :
    pairWords (fp2MulImag yst out a b) =
      Challenge.Bls12381.ProofSupport.Fp.subSource
        (fpWords (loadWord (fp2MulAfterVSumStores yst out a b).memory 1792)
          (loadWord (fp2MulAfterVSumStores yst out a b).memory 1824))
        (fpWords (loadWord (fp2MulAfterVSumStores yst out a b).memory 1856)
          (loadWord (fp2MulAfterVSumStores yst out a b).memory 1888)) := by
  exact conv_fpSubValue _ _ _ _

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
