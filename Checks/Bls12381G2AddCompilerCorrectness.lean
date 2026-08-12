import Challenge.Bls12381G2Add.Reference.Proofs.CompilerCorrectness

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.CompilerCorrectness

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.CompilerCorrectness.executionConfig_modexp_enabled' does not depend on any axioms -/
#guard_msgs in
#print axioms executionConfig_modexp_enabled

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.CompilerCorrectness.referenceCompiledBlock_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCompiledBlock_correct

