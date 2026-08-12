import Challenge.Bls12381G2Add.Reference
import Challenge.Bls12381G2Add.Scorer

set_option warningAsError true

open Challenge.Bls12381G2Add

#guard referenceBlock?.isSome
#guard optimizedReferenceBytecode?.isSome
#guard referenceNormalizedBlock?.isSome
#guard referenceBytecode?.isSome
#guard referenceBytecode? = some referenceBytecode
#guard decodedReferenceBytecode = referenceBytecode
#guard referenceBytecode.size = referenceBytecodeSize
#guard referenceBytecodeSize = 2788

#check Reference.Proofs.FinalCorrectness.reference_correct
#check Scorer.scoreReference

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨0, by decide⟩) with
  | .ok 321 => true
  | _ => false

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨2, by decide⟩) with
  | .ok 37429 => true
  | _ => false

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨4, by decide⟩) with
  | .ok 99384 => true
  | _ => false
