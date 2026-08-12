import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFirstInfinity

set_option warningAsError true

/-! # Frozen G1ADD first-infinity identity checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainFirstInfinityStmt = mainPointScopeBody[5]! := rfl

example : mainFirstInfinityStmt =
    .cond (.var "\x0096")
      [.exprStmt (.call "\x0012"
        [.builtin .mload [.lit (.number 128)],
          .builtin .mload [.lit (.number 160)],
          .builtin .mload [.lit (.number 192)],
          .builtin .mload [.lit (.number 224)]]),
       .exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := rfl

example (yst : EvmState) (hfirst : mainInf1 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainFirstInfinityStmt
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt :=
  step_mainFirstInfinity_return yst hfirst

example (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (EvmSemantics.MachineState.readPadded input 128 128).toList) :=
  mainFirstInfinity_returned_inputWindow yst input hcalldata

example (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (right : EvmSemantics.Crypto.Bls12381.Point)
    (hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 128 =
      some right) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1 right).toList) :=
  mainFirstInfinity_returned_other yst input hcalldata right hright

example (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (right : EvmSemantics.Crypto.Bls12381.Point)
    (hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 128 =
      some right) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (Challenge.Bls12381.ProofSupport.G1Affine.toWire
            (Challenge.Bls12381.ProofSupport.G1Affine.add
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire
                (.infinity : EvmSemantics.Crypto.Bls12381.Point))
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire right)))).toList) :=
  mainFirstInfinity_returned_affineIdentity
    yst input hcalldata right hright

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFirstInfinity_return' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFirstInfinity_return

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainValidatedState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainValidatedState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_storePoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_storePoint

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFirstInfinity_returned_inputWindow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFirstInfinity_returned_inputWindow

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFirstInfinity_returned_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFirstInfinity_returned_other

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFirstInfinity_returned_affineIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFirstInfinity_returned_affineIdentity

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
