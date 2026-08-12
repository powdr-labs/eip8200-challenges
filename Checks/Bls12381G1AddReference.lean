import Challenge.Bls12381G1Add.Reference
import Challenge.Bls12381G1Add.Scorer

set_option warningAsError true

open Challenge.Bls12381G1Add

#guard referenceBytecode.size = 1723
#guard referenceBytecode? = some referenceBytecode

#check Reference.Proofs.FinalCorrectness.reference_correct
#check Scorer.scoreReference

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨0, by decide⟩) with
  | .ok 177 => true
  | _ => false

#guard match Scorer.scoreReference (Scorer.vectors.get ⟨2, by decide⟩) with
  | .ok 11918 => true
  | _ => false
