import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk0
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk1
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk2
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk3
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk4
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk5
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk6
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk7
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk8
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk9
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlockChunk10
import Challenge.Bls12381G2Msm.Reference.Source
import Challenge.Bls12381G2Msm.Reference.Proofs.ComputedBlock
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk0
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk1
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk2
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk3
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk4
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk5
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk6
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk7
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk8
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk9
import Challenge.Bls12381G2Msm.Reference.Proofs.NormalizedBlockChunk10

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Frozen normalized source, assembled from independently compiled chunks. -/
def frozenReferenceBlock : Block Op :=
  frozenReferenceBlockChunk0 ++
    frozenReferenceBlockChunk1 ++
    frozenReferenceBlockChunk2 ++
    frozenReferenceBlockChunk3 ++
    frozenReferenceBlockChunk4 ++
    frozenReferenceBlockChunk5 ++
    frozenReferenceBlockChunk6 ++
    frozenReferenceBlockChunk7 ++
    frozenReferenceBlockChunk8 ++
    frozenReferenceBlockChunk9 ++
    frozenReferenceBlockChunk10

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
