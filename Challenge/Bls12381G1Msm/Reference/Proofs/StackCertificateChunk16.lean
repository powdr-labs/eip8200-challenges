import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateCore

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

private def entries := referenceStackCertificate.entries

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem stackLengthEntryChecks_chunk16 :
    stackLengthEntryChecks ((entries.drop 1600).take 100) = true := by
  with_unfolding_all decide

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
