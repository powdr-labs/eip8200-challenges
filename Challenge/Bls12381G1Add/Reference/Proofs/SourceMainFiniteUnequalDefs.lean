import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleLawful
import Challenge.Bls12381G1Add.Reference.Proofs.SourceSub

set_option warningAsError true

/-! # Frozen G1ADD unequal-x slope schedule -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFiniteUnequalBody : Block Op :=
  match mainFiniteUnequalStmt with
  | .cond _ body => body
  | _ => []

def mainFiniteUnequalStmt0 : Stmt Op := mainFiniteUnequalBody[0]!
def mainFiniteUnequalStmt1 : Stmt Op := mainFiniteUnequalBody[1]!
def mainFiniteUnequalStmt2 : Stmt Op := mainFiniteUnequalBody[2]!
def mainFiniteUnequalStmt3 : Stmt Op := mainFiniteUnequalBody[3]!

theorem mainFiniteUnequalBody_eq : mainFiniteUnequalBody =
    [mainFiniteUnequalStmt0, mainFiniteUnequalStmt1,
      mainFiniteUnequalStmt2, mainFiniteUnequalStmt3] := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
