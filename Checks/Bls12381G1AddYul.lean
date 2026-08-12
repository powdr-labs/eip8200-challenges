import Challenge.Bls12381G1Add.ProofSupport.Yul

set_option warningAsError true

open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Bls12381G1Add

example {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) :
    FrameOK code (initialState code calldata gas) :=
  ProofSupport.Yul.initialState_frameOK hsize

example {code calldata : ByteArray} {gas : Nat} :
    Challenge.EvmProof.CallerProfile executionConfig
      (initialState code calldata gas) :=
  ProofSupport.Yul.initialState_profile

/-- info: 'Challenge.Bls12381G1Add.ProofSupport.Yul.initialState_frameOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ProofSupport.Yul.initialState_frameOK

/-- info: 'Challenge.Bls12381G1Add.ProofSupport.Yul.initialState_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ProofSupport.Yul.initialState_profile
