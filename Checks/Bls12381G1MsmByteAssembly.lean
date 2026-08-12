import Challenge.Bls12381G1Msm.Reference.Proofs.ByteAssembly

set_option warningAsError true

open Challenge.Bls12381G1Msm
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

example : YulEvmCompiler.assemble referenceInstructions = referenceBytecode :=
  referenceInstructions_assemble

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.Compilation.referenceInstructions_assemble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructions_assemble
