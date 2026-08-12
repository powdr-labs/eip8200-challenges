import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpInvExec

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

#check eval_fpInv
#check fpInvOutput_eq_invCanonical

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics.eval_fpInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpInv
