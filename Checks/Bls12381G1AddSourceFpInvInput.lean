import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvInput

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM

example (hi lo : U256) (yst : EvmState) (hhi : hi.toNat < 2 ^ 128) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 96 48 =
      hi.toNat * Challenge.EvmProof.Limbs.radix + lo.toNat :=
  fpInvInput_base yst hi lo hhi

example (hi lo : U256) (yst : EvmState) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 144 48 =
      EvmSemantics.Crypto.Bls12381.p - 2 :=
  fpInvInput_exponent yst hi lo

example (hi lo : U256) (yst : EvmState) (hhi : hi.toNat < 2 ^ 128) :
    Precompile.runModexp .Osaka (fpInvInput yst hi lo) 36576 =
      .success (Precompile.natToBytes
        (Precompile.modPow
          (hi.toNat * Challenge.EvmProof.Limbs.radix + lo.toNat)
          (EvmSemantics.Crypto.Bls12381.p - 2)
          EvmSemantics.Crypto.Bls12381.p) 48) 36576 :=
  fpInvInput_runModexp hi lo yst hhi

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState_memory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpInvInputState_memory

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvInput_base

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_exponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvInput_exponent

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_modulus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvInput_modulus

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_exponentHead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvInput_exponentHead

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_gas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvInput_gas

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_runModexp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvInput_runModexp

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
