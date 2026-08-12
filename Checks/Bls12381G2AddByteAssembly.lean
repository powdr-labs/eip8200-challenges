import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssembly

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.Compilation

example : YulEvmCompiler.assemble referenceInstructions =
    Challenge.Bls12381G2Add.referenceBytecode :=
  referenceInstructions_assemble

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.Compilation.referenceInstructions_assemble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructions_assemble
