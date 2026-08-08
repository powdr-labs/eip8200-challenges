import Challenge.Ripemd160
set_option warningAsError true
/-! RIPEMD-160 axiom-footprint checks. -/

/--
info: 'Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithSchedule

/--
info: 'Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct
