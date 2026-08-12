import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenStackCertificateChunk0
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenStackCertificateChunk1
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenStackCertificateChunk2
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenStackCertificateChunk3
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssembly

set_option warningAsError true

/-! Compact G2MSM stack certificate assembled from opaque data chunks. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def frozenStackEntries : List FrozenStackEntry :=
  frozenStackEntries0 ++ frozenStackEntries1 ++
    frozenStackEntries2 ++ frozenStackEntries3

def referenceStackCertificate : YulEvmCompiler.CertData :=
  materializeStackCertificate referenceOptimizedAssembly
    (frozenStackEntries.map thawStackEntry)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
