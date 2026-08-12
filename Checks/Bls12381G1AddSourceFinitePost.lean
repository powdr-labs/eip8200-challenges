import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFinitePostLawful

set_option warningAsError true

/-! # G1ADD common post-slope checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainFinitePostBody =
    [mainFinitePostStmt0, mainFinitePostStmt1, mainFinitePostStmt2,
      mainFinitePostStmt3, mainFinitePostStmt4, mainFinitePostStmt5,
      mainFinitePostStmt6, mainFinitePostStmt7] :=
  mainFinitePostBody_eq

example : mainFinitePostStmt0 =
    Compilation.referenceCompiledBlock[28]! := rfl

example : mainFinitePostStmt7 =
    Compilation.referenceCompiledBlock[35]! := rfl

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFinitePostBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFinitePostBody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_mainFinitePostCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonical_mainFinitePostCoordinates

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFinitePostCoordinates_toLawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFinitePostCoordinates_toLawful

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFinitePostPoint_eq_add_of_x_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFinitePostPoint_eq_add_of_x_ne

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFinitePostPoint_eq_double' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFinitePostPoint_eq_double

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFinitePost_returned_codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFinitePost_returned_codec

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
