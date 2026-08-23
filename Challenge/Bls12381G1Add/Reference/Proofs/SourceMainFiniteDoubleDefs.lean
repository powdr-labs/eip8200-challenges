import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteExceptional

set_option warningAsError true

/-! # Frozen G1ADD equal-point doubling-slope schedule -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The source multiplication computing `x²`. -/
def mainFiniteDoubleStmt0 : Stmt Op := mainFiniteDoubleBody[0]!

/-- The first source addition computing `2*x²`. -/
def mainFiniteDoubleStmt1 : Stmt Op := mainFiniteDoubleBody[1]!

/-- The second source addition computing `3*x²`. -/
def mainFiniteDoubleStmt2 : Stmt Op := mainFiniteDoubleBody[2]!

/-- The source addition computing `2*y`. -/
def mainFiniteDoubleStmt3 : Stmt Op := mainFiniteDoubleBody[3]!

/-- The source inversion computing `(2*y)⁻¹`. -/
def mainFiniteDoubleStmt4 : Stmt Op := mainFiniteDoubleBody[4]!

/-- The source multiplication assigning the doubling slope. -/
def mainFiniteDoubleStmt5 : Stmt Op := mainFiniteDoubleBody[5]!

theorem mainFiniteDoubleBody_eq : mainFiniteDoubleBody =
    [mainFiniteDoubleStmt0, mainFiniteDoubleStmt1,
      mainFiniteDoubleStmt2, mainFiniteDoubleStmt3,
      mainFiniteDoubleStmt4, mainFiniteDoubleStmt5] := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
