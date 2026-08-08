import Challenge.Sha256
set_option warningAsError true
/-! SHA-256 axiom-footprint checks. -/

/-
The dynamic submission checker applies the same discipline to every discovered
candidate theorem, allowing any subset of the standard classical axioms and
rejecting every project-defined or computational escape-hatch axiom.
-/

/--
info: 'Challenge.Sha256.ProofSupport.Bytecode.correct_of_directProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.ProofSupport.Bytecode.correct_of_directProof

/--
info: 'Challenge.Sha256.Reference.Proofs.Bytecode.Reference.reaches_firstTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.Reference.Proofs.Bytecode.Reference.reaches_firstTarget

/--
info: 'Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.referenceDirectProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.referenceDirectProof

/--
info: 'Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

/-- info: 'Challenge.Sha256.correct_of_computesDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Sha256.correct_of_computesDigest

/-- info: 'Challenge.Sha256.correct_of_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Sha256.correct_of_schedule

/-- info: 'Challenge.Sha256.initialState_frameOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Sha256.initialState_frameOK
