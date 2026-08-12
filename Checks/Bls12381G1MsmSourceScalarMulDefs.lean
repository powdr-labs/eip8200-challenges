import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulDefs

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check scalarMulBody
#check scalarMulBody_eq
#check scalarMulLoopBody_eq
#check scalarMulLoopPost_eq
#check lookup_scalarMul
#print axioms scalarMulBody_eq
#print axioms lookup_scalarMul
