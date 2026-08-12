import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulInput

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo })
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }) :
    Precompile.runModexp .Osaka
        (Challenge.EvmProof.ModexpMemory.readWindow
          (fpMulInputState yst ahi alo bhi blo).memory 1024 241)
        500 =
      .success (Precompile.natToBytes
        ((Challenge.Bls12381.ProofSupport.Fp.value
            { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo } *
          Challenge.Bls12381.ProofSupport.Fp.value
            { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }) %
          EvmSemantics.Crypto.Bls12381.p) 48) 500 :=
  fpMulInput_runModexp ahi alo bhi blo yst ha hb

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInputState_memory' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInputState_memory

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_baseSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_baseSize

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_exponentSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_exponentSize

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_modulusSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_modulusSize

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_exponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_exponent

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_modulus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_modulus

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_base

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_runModexp_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_runModexp_raw

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_runModexp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulInput_runModexp

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
