import Challenge.Bls12381G1Add.Reference.Proofs.SourceSpec

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

#check run_matches_spec

example (yst : YulSemantics.EVM.EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (hfit : input.size < 2 ^ 256) (hhalted : yst.halted = none) :=
  run_matches_spec yst input hcalldata hfit hhalted

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.decodeG1_first_eq_sourcePoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms decodeG1_first_eq_sourcePoint

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.decodeG1_second_eq_sourcePoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms decodeG1_second_eq_sourcePoint

/--
info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_matches_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms run_matches_spec
