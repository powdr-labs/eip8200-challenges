import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulRefinement

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Challenge.Bls12381.ProofSupport.Fp.value
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      (convFullMul (fullMulValue ahi alo bhi blo)).value %
        EvmSemantics.Crypto.Bls12381.p :=
  fpMulOutput_value yst ahi alo bhi blo

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulOutputLimbs yst ahi alo bhi blo) :=
  canonical_fpMulOutput yst ahi alo bhi blo

example (ahi alo bhi blo : U256) (yst : EvmState)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulRight bhi blo)) :
    Challenge.Bls12381.ProofSupport.Fp.toField
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.toField (fpMulLeft ahi alo) *
        Challenge.Bls12381.ProofSupport.Fp.toField (fpMulRight bhi blo) :=
  fpMulOutput_toField yst ahi alo bhi blo ha hb

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulOutput_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulOutput_value

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_fpMulOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonical_fpMulOutput

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulOutput_toField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulOutput_toField

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
