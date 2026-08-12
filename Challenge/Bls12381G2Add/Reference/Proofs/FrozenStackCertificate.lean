import Challenge.Bls12381G2Add.Reference.Proofs.FrozenStackCertificateChunk0
import Challenge.Bls12381G2Add.Reference.Proofs.FrozenStackCertificateChunk1
import Challenge.Bls12381G2Add.Reference.Proofs.FrozenStackCertificateChunk2

set_option warningAsError true

/-! Compact G2ADD stack certificate assembled from opaque data chunks. -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

def frozenStackEntries : List FrozenStackEntry :=
  frozenStackEntries0 ++ frozenStackEntries1 ++ frozenStackEntries2

def referenceStackCertificate : YulEvmCompiler.CertData :=
  materializeStackCertificate referenceOptimizedAssembly
    (frozenStackEntries.map thawStackEntry)

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation

