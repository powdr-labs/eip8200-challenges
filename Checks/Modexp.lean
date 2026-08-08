import Challenge.Modexp
set_option warningAsError true
/-! MODEXP axiom-footprint checks. -/

/--
info: 'Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect.referenceDirectProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect.referenceDirectProof

/--
info: 'Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

/--
info: 'Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect.gasSteps_reference_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect.gasSteps_reference_cost

/-- info: 'Challenge.Modexp.Reference.Proofs.Gas.gasSchedule_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Modexp.Reference.Proofs.Gas.gasSchedule_correct
