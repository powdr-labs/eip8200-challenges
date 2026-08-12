import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteExceptional

set_option warningAsError true

/-! # G1ADD finite exceptional-branch checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (yst : EvmState) (hyeq : mainFiniteYEqValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteOppositeStmt (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt :=
  step_mainFiniteOpposite_return yst hyeq

example (yst : EvmState) (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYEqArgsState yst)
      mainFiniteZeroYStmt (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt :=
  step_mainFiniteZeroY_return yst hyzero

example (yst : EvmState) (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst) mainFiniteEqualStmt
      (mainFiniteEnv yst) (mainFiniteOppositeReturnState yst) .halt :=
  step_mainFiniteEqual_opposite yst hxeq hyeq

example (yst : EvmState) (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst) mainFiniteEqualStmt
      (mainFiniteEnv yst) (mainFiniteZeroYReturnState yst) .halt :=
  step_mainFiniteEqual_zeroY yst hxeq hyeq hyzero

example (yst : EvmState) :
    (mainFiniteOppositeReturnState yst).halted =
      some (HaltKind.ret, List.replicate 128 0) :=
  mainFiniteOpposite_returned_zero_bytes yst

example (yst : EvmState) :
    (mainFiniteZeroYReturnState yst).halted =
      some (HaltKind.ret, List.replicate 128 0) :=
  mainFiniteZeroY_returned_zero_bytes yst

example (yst : EvmState) :
    (mainFiniteOppositeReturnState yst).halted =
      some (HaltKind.ret,
        Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (.infinity : EvmSemantics.Crypto.Bls12381.Point) |>.toList) :=
  mainFiniteOpposite_returned_codec yst

example (yst : EvmState) :
    (mainFiniteZeroYReturnState yst).halted =
      some (HaltKind.ret,
        Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (.infinity : EvmSemantics.Crypto.Bls12381.Point) |>.toList) :=
  mainFiniteZeroY_returned_codec yst

example (x y1 y2 : Challenge.Bls12381.ProofSupport.G1Affine.Field)
    (hopposite : y1 + y2 = 0) :
    Challenge.Bls12381.ProofSupport.G1Affine.add
      (.affine x y1) (.affine x y2) = .infinity :=
  mainFiniteOpposite_affineInfinity x y1 y2 hopposite

example (x : Challenge.Bls12381.ProofSupport.G1Affine.Field) :
    Challenge.Bls12381.ProofSupport.G1Affine.double
      (.affine x 0) = .infinity :=
  mainFiniteZeroY_affineInfinity x

example (yst : EvmState) (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteYZeroArgsState yst).memory offset =
      mainDecodedWord yst offset :=
  mainFiniteYZeroArgsState_loadWord yst offset hend

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteOpposite_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteOpposite_return

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteZeroY_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteZeroY_return

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteEqual_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteEqual_opposite

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteEqual_zeroY' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteEqual_zeroY

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteOpposite_returned_zero_bytes' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteOpposite_returned_zero_bytes

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteZeroY_returned_zero_bytes' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteZeroY_returned_zero_bytes

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteOpposite_returned_codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteOpposite_returned_codec

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteZeroY_returned_codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteZeroY_returned_codec

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteOpposite_affineInfinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteOpposite_affineInfinity

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteZeroY_affineInfinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteZeroY_affineInfinity

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteYZeroArgsState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteYZeroArgsState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.afterFourLoads_memory' does not depend on any axioms -/
#guard_msgs in
#print axioms afterFourLoads_memory

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpEqLoads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpEqLoads

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.afterTwoLoads_memory' does not depend on any axioms -/
#guard_msgs in
#print axioms afterTwoLoads_memory

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
