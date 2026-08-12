import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteClassify

set_option warningAsError true

/-! # Frozen G1ADD finite classification checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainFiniteSlopeDecl =
    Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock[25]! := rfl

example : mainFiniteEqualStmt =
    Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock[26]! := rfl

example : mainFiniteUnequalStmt =
    Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock[27]! := rfl

example : mainFiniteOppositeStmt = mainFiniteEqualBody[0]! := rfl

example : mainFiniteZeroYStmt = mainFiniteEqualBody[1]! := rfl

example : mainFiniteEqualBody =
    mainFiniteOppositeStmt :: mainFiniteZeroYStmt :: mainFiniteDoubleBody :=
  mainFiniteEqualBody_eq

example : mainFiniteOppositeStmt =
    .cond
      (.builtin .iszero
        [.call "\x003"
          [.builtin .mload [.lit (.number 64)],
            .builtin .mload [.lit (.number 96)],
            .builtin .mload [.lit (.number 192)],
            .builtin .mload [.lit (.number 224)]]])
      [.exprStmt (.call "\x0012"
        [.lit (.number 0), .lit (.number 0),
          .lit (.number 0), .lit (.number 0)]),
       .exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := rfl

example : mainFiniteZeroYStmt =
    .cond
      (.call "\x002"
        [.builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])
      [.exprStmt (.call "\x0012"
        [.lit (.number 0), .lit (.number 0),
          .lit (.number 0), .lit (.number 0)]),
       .exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := rfl

example (aHi aLo bHi bLo : U256) :
    fpEqValue aHi aLo bHi bLo = 1 ↔ aHi = bHi ∧ aLo = bLo :=
  fpEqValue_eq_one_iff _ _ _ _

example (aHi aLo bHi bLo : U256) :
    fpEqValue aHi aLo bHi bLo = 0 ↔ aHi ≠ bHi ∨ aLo ≠ bLo :=
  fpEqValue_eq_zero_iff _ _ _ _

example (yst : EvmState) :
    mainFiniteXEqValue yst = 1 ↔
      mainDecodedWord yst 0 = mainDecodedWord yst 128 ∧
      mainDecodedWord yst 32 = mainDecodedWord yst 160 :=
  mainFiniteXEq_eq_one_iff yst

example (yst : EvmState) :
    mainFiniteYEqValue yst = 0 ↔
      mainDecodedWord yst 64 ≠ mainDecodedWord yst 192 ∨
      mainDecodedWord yst 96 ≠ mainDecodedWord yst 224 :=
  mainFiniteYEq_eq_zero_iff yst

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpEqValue_eq_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fpEqValue_eq_one_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpEqValue_eq_zero_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpEqValue_eq_zero_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteXEq_eq_one_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteXEq_eq_one_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteXEq_eq_zero_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteXEq_eq_zero_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteYEq_eq_one_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteYEq_eq_one_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteYEq_eq_zero_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteYEq_eq_zero_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteEqualBody_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mainFiniteEqualBody_eq

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
