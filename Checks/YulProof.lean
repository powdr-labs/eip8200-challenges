import Challenge.YulProof

set_option warningAsError true

/-! Axiom-footprint checks for shared source-Yul proof support. -/

/-- info: 'Challenge.YulProof.ClosedEvm.exec_lawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.YulProof.ClosedEvm.exec_lawful

/-- info: 'Challenge.YulProof.Interpreter.execLoop_of_interp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.YulProof.Interpreter.execLoop_of_interp

/-- info: 'Challenge.YulProof.EvmState.loadWord_storeMany_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.YulProof.EvmState.loadWord_storeMany_preserved

/-- info: 'Challenge.YulProof.Limbs.copyWordsState_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.YulProof.Limbs.copyWordsState_preserves
