import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainSecondInfinity

set_option warningAsError true

/-! # Frozen G1ADD second-infinity identity checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainSecondInfinityStmt = mainPointScopeBody[6]! := rfl

example : mainSecondInfinityStmt =
    .cond (.var "\x0097")
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := rfl

example (yst : EvmState) (hsecond : mainInf2 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainSecondInfinityStmt
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt :=
  step_mainSecondInfinity_return yst hsecond

example (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (EvmSemantics.MachineState.readPadded input 0 128).toList) :=
  mainSecondInfinity_returned_inputWindow yst input hcalldata

example (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (left : EvmSemantics.Crypto.Bls12381.Point)
    (hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 =
      some left) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1 left).toList) :=
  mainSecondInfinity_returned_other yst input hcalldata left hleft

example (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (left : EvmSemantics.Crypto.Bls12381.Point)
    (hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 =
      some left) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (Challenge.Bls12381.ProofSupport.G1Affine.toWire
            (Challenge.Bls12381.ProofSupport.G1Affine.add
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire left)
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire
                (.infinity : EvmSemantics.Crypto.Bls12381.Point))))).toList) :=
  mainSecondInfinity_returned_affineIdentity
    yst input hcalldata left hleft

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainSecondInfinity_return' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainSecondInfinity_return

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainSecondInfinity_returned_inputWindow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainSecondInfinity_returned_inputWindow

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainSecondInfinity_returned_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainSecondInfinity_returned_other

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainSecondInfinity_returned_affineIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainSecondInfinity_returned_affineIdentity

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
