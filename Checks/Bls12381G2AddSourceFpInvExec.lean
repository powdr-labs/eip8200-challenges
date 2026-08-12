import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpInvExec

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check exec_fpInvStores
#check exec_fpInvCall
#check exec_fpInvBody

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.eval_fpInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpInv

