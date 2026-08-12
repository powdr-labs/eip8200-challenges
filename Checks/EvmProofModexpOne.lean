import Challenge.EvmProof.ModexpOne

set_option warningAsError true

namespace Challenge.EvmProof.ModexpOne

open EvmSemantics.EVM

example (input : ByteArray) (base modulus : Nat)
    (hbaseSize : Precompile.bytesToNatPadded input 0 32 = 96)
    (hexponentSize : Precompile.bytesToNatPadded input 32 32 = 1)
    (hmodulusSize : Precompile.bytesToNatPadded input 64 32 = 48)
    (hbase : Precompile.bytesToNatPadded input 96 96 = base)
    (hexponent : Precompile.bytesToNatPadded input 192 1 = 1)
    (hmodulus : Precompile.bytesToNatPadded input 193 48 = modulus)
    (hmodulusOne : 1 < modulus) :
    Precompile.runModexp .Osaka input 500 =
      .success (Precompile.natToBytes (base % modulus) 48) 500 :=
  runModexp_96_1_48 hbaseSize hexponentSize hmodulusSize hbase
    hexponent hmodulus hmodulusOne

/-- info: 'Challenge.EvmProof.ModexpOne.runModexp_96_1_48' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runModexp_96_1_48

end Challenge.EvmProof.ModexpOne
