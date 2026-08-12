import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDefs

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check pointAddUnequalCode_eq
#check pointAddUnequalNumeratorBody_eq
#check pointAddUnequalDenominatorBody_eq

/-- info: 'Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics.pointAddUnequalCode_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pointAddUnequalCode_eq
