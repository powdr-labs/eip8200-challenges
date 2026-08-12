import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk0
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk1
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk2
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk3
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk4
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk5
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk6
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk7
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk8
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk9
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk10
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk11
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk12
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk13
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk14
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk15
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk16
import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunk17

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

set_option maxRecDepth 50000 in
theorem referenceStackLengthEntryChecks :
    stackLengthEntryChecks referenceStackCertificate.entries = true := by
  have h18 : stackLengthEntryChecks
      (referenceStackCertificate.entries.drop 1800) = true := by
    rfl
  have h17 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1700) 100
    stackLengthEntryChecks_chunk17 (by simpa [List.drop_drop] using h18)
  have h16 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1600) 100
    stackLengthEntryChecks_chunk16 (by simpa [List.drop_drop] using h17)
  have h15 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1500) 100
    stackLengthEntryChecks_chunk15 (by simpa [List.drop_drop] using h16)
  have h14 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1400) 100
    stackLengthEntryChecks_chunk14 (by simpa [List.drop_drop] using h15)
  have h13 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1300) 100
    stackLengthEntryChecks_chunk13 (by simpa [List.drop_drop] using h14)
  have h12 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1200) 100
    stackLengthEntryChecks_chunk12 (by simpa [List.drop_drop] using h13)
  have h11 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1100) 100
    stackLengthEntryChecks_chunk11 (by simpa [List.drop_drop] using h12)
  have h10 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 1000) 100
    stackLengthEntryChecks_chunk10 (by simpa [List.drop_drop] using h11)
  have h9 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 900) 100
    stackLengthEntryChecks_chunk9 (by simpa [List.drop_drop] using h10)
  have h8 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 800) 100
    stackLengthEntryChecks_chunk8 (by simpa [List.drop_drop] using h9)
  have h7 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 700) 100
    stackLengthEntryChecks_chunk7 (by simpa [List.drop_drop] using h8)
  have h6 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 600) 100
    stackLengthEntryChecks_chunk6 (by simpa [List.drop_drop] using h7)
  have h5 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 500) 100
    stackLengthEntryChecks_chunk5 (by simpa [List.drop_drop] using h6)
  have h4 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 400) 100
    stackLengthEntryChecks_chunk4 (by simpa [List.drop_drop] using h5)
  have h3 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 300) 100
    stackLengthEntryChecks_chunk3 (by simpa [List.drop_drop] using h4)
  have h2 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 200) 100
    stackLengthEntryChecks_chunk2 (by simpa [List.drop_drop] using h3)
  have h1 := stackLengthEntryChecks_take_drop
    (referenceStackCertificate.entries.drop 100) 100
    stackLengthEntryChecks_chunk1 (by simpa [List.drop_drop] using h2)
  exact stackLengthEntryChecks_take_drop
    referenceStackCertificate.entries 100
    stackLengthEntryChecks_chunk0 (by simpa [List.drop_drop] using h1)

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
