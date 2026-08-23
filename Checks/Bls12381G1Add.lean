import Challenge.Bls12381G1Add

set_option warningAsError true

/-! BLS12-381 G1ADD source-proof axiom guards. -/

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.Yul.referenceNormalized_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.Yul.referenceNormalized_correct

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.Yul.referenceParsedBlock_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceNormalizedBlock_eq._native.native_decide.ax_1_1,
 Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceParseSucceeded._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Challenge.Bls12381G1Add.Reference.Proofs.Yul.referenceParsedBlock_correct
