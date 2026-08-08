import Challenge.Blake2f
set_option warningAsError true
/-! BLAKE2f axiom-footprint checks. -/

/--
info: 'Challenge.Blake2f.ProofSupport.Bytecode.correct_of_directProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.ProofSupport.Bytecode.correct_of_directProof

/-- info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.run

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.gasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.gasSteps_cost

/-- info: 'Challenge.Blake2f.ProofSupport.Algorithm.mixLanesEVM_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Blake2f.ProofSupport.Algorithm.mixLanesEVM_embed

/-- info: 'Challenge.Blake2f.ProofSupport.Algorithm.lanesAt_crypto_mixG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Blake2f.ProofSupport.Algorithm.lanesAt_crypto_mixG

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.MixGCorrectness.lanesAt_transition_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.MixGCorrectness.lanesAt_transition_embed

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.hLoopGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.hLoopGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.mLoopGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.mLoopGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.vLoopGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.vLoopGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.constantsGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.constantsGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps_cost

/-
The entire valid-input prefix, through calldata decoding and work-vector setup,
is certified without any project axioms beyond Lean's standard quotient and
extensionality foundations.
-/
/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.fullGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.fullGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Round.iterationGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Round.iterationGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Round.loopGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Round.loopGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.iterationSafe_of_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.iterationSafe_of_schedule

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.schedule_finalMemory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.schedule_finalMemory

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.MixGCorrectness.representsAt_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.MixGCorrectness.representsAt_transition

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.memoryModel_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.memoryModel_transition

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.memoryModel_memories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness.memoryModel_memories

/-
The completed functional, execution, and gas theorems use only Lean's standard
logical foundations. In particular, the direct bytecode theorem does not
depend on the finite `native_decide` compiler-reproducibility checks.
-/
/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.OutputCorrectness.finalState_return_eq_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.OutputCorrectness.finalState_return_eq_spec

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.validGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.validGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithExactGas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithExactGas

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithSchedule

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

/-- info: 'Challenge.Blake2f.Reference.Proofs.Gas.gasSchedule_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Gas.gasSchedule_correct
