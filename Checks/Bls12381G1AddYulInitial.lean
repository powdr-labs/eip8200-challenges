import Challenge.Bls12381G1Add.ProofSupport.YulInitial

set_option warningAsError true

open Challenge.Bls12381G1Add
open Challenge.Bls12381G1Add.ProofSupport.Yul

#check sourceInitialState_matches

example (code calldata : ByteArray) (gas : Nat) :
    YulEvmCompiler.StateMatch (sourceInitialState code calldata)
      (initialState code calldata gas) :=
  sourceInitialState_matches code calldata gas

/--
info: 'Challenge.Bls12381G1Add.ProofSupport.Yul.sourceInitialState_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceInitialState_matches
