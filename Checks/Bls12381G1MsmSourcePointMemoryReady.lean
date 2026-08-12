import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointMemoryReady

set_option warningAsError true

open Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

#check PointMemoryRegion
#check PointAddMemoryInvariant
#check PointAddMemoryInvariant.pointAddReady
