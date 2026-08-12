import Challenge.Bls12381G2Msm.Reference
import Challenge.Bls12381G2Msm.Scorer

set_option warningAsError true

open Challenge.Bls12381G2Msm

#guard referenceBlock?.isSome
#guard referenceNormalizedBlock?.isSome
#guard referenceBytecode?.isSome
#guard referenceBytecode? = some referenceBytecode
#guard decodedReferenceBytecode = referenceBytecode
#guard referenceBytecode.size = referenceBytecodeSize
#guard referenceBytecodeSize = 3264

#check Scorer.scoreReference

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨0, by decide⟩) with
  | .ok _ => true
  | _ => false

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨2, by decide⟩) with
  | .ok _ => true
  | _ => false

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨4, by decide⟩) with
  | .ok _ => true
  | _ => false
