import Challenge.Bls12381G1Add.Reference.Proofs.SourceInput

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

#check mainDecodedWord_eq_input
#check decodeFp_eq_some_sourceField
#check mainPaddingValue_eq_zero_iff_codec
#check decodeFp_eq_none_iff_sourceField

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainDecodedWord_eq_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mainDecodedWord_eq_input

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.decodeFp_eq_some_sourceField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms decodeFp_eq_some_sourceField

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainPaddingValue_eq_zero_iff_codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mainPaddingValue_eq_zero_iff_codec

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.decodeFp_eq_none_iff_sourceField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms decodeFp_eq_none_iff_sourceField
