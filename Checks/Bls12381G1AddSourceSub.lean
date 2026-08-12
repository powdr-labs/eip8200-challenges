import Challenge.Bls12381G1Add.Reference.Proofs.SourceSub

set_option warningAsError true

open YulSemantics.EVM

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

example (ahi alo bhi blo : U256) :
    convPair (fpSubRawValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.subRaw
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  conv_fpSubRawValue ahi alo bhi blo

example (diff : U256 × U256) :
    YulEvmCompiler.conv (fpSubNeedsRepairValue diff) =
      EvmSemantics.UInt256.gt (convPair diff).hi
        Challenge.Bls12381.ProofSupport.Fp.modulusHi :=
  conv_fpSubNeedsRepairValue diff

example (diff : U256 × U256) :
    convPair (fpSubRepairValue diff) =
      Challenge.Bls12381.ProofSupport.Fp.subRepair (convPair diff) :=
  conv_fpSubRepairValue diff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubRepairValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fpSubRepairValue

example (ahi alo bhi blo : U256) :
    convPair (fpSubValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.subSource
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  conv_fpSubValue ahi alo bhi blo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fpSubValue

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubRawValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fpSubRawValue

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubNeedsRepairValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fpSubNeedsRepairValue

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
