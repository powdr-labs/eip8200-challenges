import Challenge.Bls12381G1Msm.Reference.Proofs.BackendCompile

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

example :
    YulEvmCompiler.compileProgram referenceBackendBlock =
      some referenceAssembly :=
  referenceBackendBlock_compileProgram

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.Compilation.referenceBackendBlock_compileProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceBackendBlock_compileProgram
