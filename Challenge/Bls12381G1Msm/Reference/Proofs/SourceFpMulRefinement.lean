import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulExec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulRefinement

set_option warningAsError true

/-! Lawful field refinement of the frozen G1MSM `fpMul` result. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fpMulCallState_eq_shared (yst : EvmState) (ahi alo bhi blo : U256) :
    fpMulCallState yst ahi alo bhi blo =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulCallState
        yst ahi alo bhi blo := by
  rfl

theorem fpMulResult_eq_shared (yst : EvmState) (ahi alo bhi blo : U256) :
    fpMulResult yst ahi alo bhi blo =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulResult
        yst ahi alo bhi blo := by
  rfl

abbrev fpMulOutputLimbs :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulOutputLimbs

abbrev fpMulLeft :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulLeft

abbrev fpMulRight :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulRight

theorem canonical_fpMulOutput (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulOutputLimbs yst ahi alo bhi blo) := by
  exact
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_fpMulOutput
      yst ahi alo bhi blo

theorem fpMulOutput_toField (yst : EvmState) (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulRight bhi blo)) :
    Challenge.Bls12381.ProofSupport.Fp.toField
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.toField (fpMulLeft ahi alo) *
        Challenge.Bls12381.ProofSupport.Fp.toField (fpMulRight bhi blo) := by
  exact
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulOutput_toField
      yst ahi alo bhi blo ha hb

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
