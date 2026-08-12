import Challenge.Bls12381G2Add.ProofSupport.Yul

set_option warningAsError true

open Challenge.Bls12381G2Add
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

example {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) :
    YulEvmCompiler.FrameOK code (initialState code calldata gas) :=
  ProofSupport.Yul.initialState_frameOK hsize

example {code calldata : ByteArray} {gas : Nat} :
    CallerProfile executionConfig (initialState code calldata gas) :=
  ProofSupport.Yul.initialState_profile

/-- info: 'Challenge.Bls12381G2Add.ProofSupport.Yul.initialState_frameOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.ProofSupport.Yul.initialState_frameOK

/-- info: 'Challenge.Bls12381G2Add.ProofSupport.Yul.initialState_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Bls12381G2Add.ProofSupport.Yul.initialState_profile
