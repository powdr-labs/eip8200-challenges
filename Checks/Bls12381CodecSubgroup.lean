import Challenge.Bls12381.ProofSupport.CodecSubgroup

set_option warningAsError true

namespace Checks.Bls12381CodecSubgroup

open EvmSemantics.Crypto.Bls12381
open Challenge.Bls12381.ProofSupport

example (input : ByteArray) (offset : Nat) (point : Point) :
    Codec.decodeG1Subgroup input offset = some point ↔
      Codec.decodeG1 input offset = some point ∧ Subgroup.g1 point = true :=
  Codec.decodeG1Subgroup_eq_some_iff input offset point

example (input : ByteArray) (offset : Nat) (point : G2Point) :
    Codec.decodeG2Subgroup input offset = some point ↔
      Codec.decodeG2 input offset = some point ∧ Subgroup.g2 point = true :=
  Codec.decodeG2Subgroup_eq_some_iff input offset point

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1Subgroup_eq_some_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1Subgroup_eq_some_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2Subgroup_eq_some_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2Subgroup_eq_some_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG1Subgroup_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG1Subgroup_forget

/-- info: 'Challenge.Bls12381.ProofSupport.Codec.decodeG2Subgroup_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Codec.decodeG2Subgroup_forget

end Checks.Bls12381CodecSubgroup
