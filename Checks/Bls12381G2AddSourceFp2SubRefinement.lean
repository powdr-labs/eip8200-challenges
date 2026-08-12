import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubRefinement

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check fp2SubResult_eq_subSource
#check fp2SubResult_canonical
#check fp2SubResult_toField

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubResult_eq_subSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2SubResult_eq_subSource
