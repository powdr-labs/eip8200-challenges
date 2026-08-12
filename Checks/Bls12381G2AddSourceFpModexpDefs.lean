import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpModexpDefs

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

example : fpMulBody.length = 12 := by decide
example : fpInvBody.length = 9 := by decide

#check lookup_fpMul
#check lookup_fpInv
#check fpMulOutput_eq_mulCanonical
#check fpInvOutput_eq_invCanonical

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulOutput_eq_mulCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulOutput_eq_mulCanonical

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvOutput_eq_invCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvOutput_eq_invCanonical

