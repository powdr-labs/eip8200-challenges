import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteUnequalLawful

set_option warningAsError true

/-! # Frozen G1ADD common post-slope schedule -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFinitePostBody : Block Op :=
  Compilation.referenceCompiledBlock.drop 28

def mainFinitePostStmt0 : Stmt Op := mainFinitePostBody[0]!
def mainFinitePostStmt1 : Stmt Op := mainFinitePostBody[1]!
def mainFinitePostStmt2 : Stmt Op := mainFinitePostBody[2]!
def mainFinitePostStmt3 : Stmt Op := mainFinitePostBody[3]!
def mainFinitePostStmt4 : Stmt Op := mainFinitePostBody[4]!
def mainFinitePostStmt5 : Stmt Op := mainFinitePostBody[5]!
def mainFinitePostStmt6 : Stmt Op := mainFinitePostBody[6]!
def mainFinitePostStmt7 : Stmt Op := mainFinitePostBody[7]!

theorem mainFinitePostBody_eq : mainFinitePostBody =
    [mainFinitePostStmt0, mainFinitePostStmt1, mainFinitePostStmt2,
      mainFinitePostStmt3, mainFinitePostStmt4, mainFinitePostStmt5,
      mainFinitePostStmt6, mainFinitePostStmt7] := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
