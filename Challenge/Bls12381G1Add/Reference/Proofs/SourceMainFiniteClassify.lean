import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainSecondInfinity

set_option warningAsError true

/-! # Frozen G1ADD finite-point classification -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The two-word slope declaration immediately following the scoped infinity
branches. -/
def mainFiniteSlopeDecl : Stmt Op :=
  Compilation.referenceCompiledBlock[25]!

/-- The equal-x (doubling/opposite) dispatch. -/
def mainFiniteEqualStmt : Stmt Op :=
  Compilation.referenceCompiledBlock[26]!

/-- The unequal-x general-addition dispatch. -/
def mainFiniteUnequalStmt : Stmt Op :=
  Compilation.referenceCompiledBlock[27]!

def mainFiniteEqualBody : Block Op :=
  match mainFiniteEqualStmt with
  | .cond _ body => body
  | _ => []

/-- Equal-x points with unequal y coordinates take the vertical-tangent
infinity branch. -/
def mainFiniteOppositeStmt : Stmt Op := mainFiniteEqualBody[0]!

/-- Equal-x/equal-y points with `y = 0` take the explicit doubling-at-vertical-
tangent infinity branch. -/
def mainFiniteZeroYStmt : Stmt Op := mainFiniteEqualBody[1]!

/-- The remaining equal-point doubling arithmetic after its two exceptional
guards. -/
def mainFiniteDoubleBody : Block Op := mainFiniteEqualBody.drop 2

theorem mainFiniteEqualBody_eq : mainFiniteEqualBody =
    mainFiniteOppositeStmt :: mainFiniteZeroYStmt :: mainFiniteDoubleBody := by
  rfl

/-- Exact source equality classification for the finite points' x words. -/
def mainFiniteXEqValue (yst : EvmState) : U256 :=
  fpEqValue (mainDecodedWord yst 0) (mainDecodedWord yst 32)
    (mainDecodedWord yst 128) (mainDecodedWord yst 160)

/-- Exact source equality classification for the finite points' y words. -/
def mainFiniteYEqValue (yst : EvmState) : U256 :=
  fpEqValue (mainDecodedWord yst 64) (mainDecodedWord yst 96)
    (mainDecodedWord yst 192) (mainDecodedWord yst 224)

/-- `fpEq` returns one exactly when both source words agree. -/
theorem fpEqValue_eq_one_iff (aHi aLo bHi bLo : U256) :
    fpEqValue aHi aLo bHi bLo = 1 ↔ aHi = bHi ∧ aLo = bLo := by
  simp only [fpEqValue]
  by_cases hHi : aHi = bHi <;> by_cases hLo : aLo = bLo <;>
    simp [b2w, hHi, hLo]

/-- `fpEq` returns zero exactly when at least one source word differs. -/
theorem fpEqValue_eq_zero_iff (aHi aLo bHi bLo : U256) :
    fpEqValue aHi aLo bHi bLo = 0 ↔ aHi ≠ bHi ∨ aLo ≠ bLo := by
  simp only [fpEqValue]
  by_cases hHi : aHi = bHi <;> by_cases hLo : aLo = bLo <;>
    simp [b2w, hHi, hLo]

theorem mainFiniteXEq_eq_one_iff (yst : EvmState) :
    mainFiniteXEqValue yst = 1 ↔
      mainDecodedWord yst 0 = mainDecodedWord yst 128 ∧
      mainDecodedWord yst 32 = mainDecodedWord yst 160 := by
  exact fpEqValue_eq_one_iff _ _ _ _

theorem mainFiniteXEq_eq_zero_iff (yst : EvmState) :
    mainFiniteXEqValue yst = 0 ↔
      mainDecodedWord yst 0 ≠ mainDecodedWord yst 128 ∨
      mainDecodedWord yst 32 ≠ mainDecodedWord yst 160 := by
  exact fpEqValue_eq_zero_iff _ _ _ _

theorem mainFiniteYEq_eq_one_iff (yst : EvmState) :
    mainFiniteYEqValue yst = 1 ↔
      mainDecodedWord yst 64 = mainDecodedWord yst 192 ∧
      mainDecodedWord yst 96 = mainDecodedWord yst 224 := by
  exact fpEqValue_eq_one_iff _ _ _ _

theorem mainFiniteYEq_eq_zero_iff (yst : EvmState) :
    mainFiniteYEqValue yst = 0 ↔
      mainDecodedWord yst 64 ≠ mainDecodedWord yst 192 ∨
      mainDecodedWord yst 96 ≠ mainDecodedWord yst 224 := by
  exact fpEqValue_eq_zero_iff _ _ _ _

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
