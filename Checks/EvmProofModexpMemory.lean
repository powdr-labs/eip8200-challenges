import Challenge.EvmProof.ModexpMemory

set_option warningAsError true

namespace Challenge.EvmProof.ModexpMemory

open EvmSemantics

example (memory : Nat → UInt8) (start : Nat) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory start (0#256)) start 32 =
      List.replicate 32 0 :=
  readBytes_storeWord_zero memory start

example (memory : Nat → UInt8) (destination source : Nat)
    (input : ByteArray) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory destination
          (YulSemantics.EVM.wordFrom input.toList source))
        destination 32 =
      (EvmSemantics.MachineState.readPadded input source 32).toList :=
  readBytes_storeWord_wordFrom memory destination source input

/-- info: 'Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readBytes_storeWord_wordFrom

/-- info: 'Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_storeWord_zero

example (memory : Nat → UInt8) (start size : Nat) :
    (readWindow memory start size).size = size :=
  readWindow_size memory start size

example (memory : Nat → UInt8) (start left right : Nat) :
    YulSemantics.EVM.readBytes memory start (left + right) =
      YulSemantics.EVM.readBytes memory start left ++
        YulSemantics.EVM.readBytes memory (start + left) right :=
  readBytes_add memory start left right

/-- info: 'Challenge.EvmProof.ModexpMemory.readBytes_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_add

example (memory : Nat → UInt8) (readStart readSize writeStart : Nat)
    (value : YulSemantics.EVM.U256)
    (hdisjoint : readStart + readSize ≤ writeStart ∨
      writeStart + 32 ≤ readStart) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeWord memory writeStart value)
        readStart readSize =
      YulSemantics.EVM.readBytes memory readStart readSize :=
  readBytes_storeWord_disjoint memory readStart readSize writeStart value
    hdisjoint

example (memory : Nat → UInt8) (readStart readSize writeStart : Nat)
    (value : YulSemantics.EVM.U256)
    (hdisjoint : readStart + readSize ≤ writeStart ∨
      writeStart < readStart) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.storeByte memory writeStart value)
        readStart readSize =
      YulSemantics.EVM.readBytes memory readStart readSize :=
  readBytes_storeByte_disjoint memory readStart readSize writeStart value
    hdisjoint

/-- info: 'Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_storeWord_disjoint

/-- info: 'Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_storeByte_disjoint

example (memory : Nat → UInt8) (start size offset width : Nat)
    (hfit : offset + width ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset width =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) width) :=
  bytesToNatPadded_readWindow memory start size offset width hfit

example (memory : Nat → UInt8) (start size offset : Nat)
    (hfit : offset + 32 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 32 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 32) :=
  bytesToNatPadded_readWindow32 memory start size offset hfit

example (memory : Nat → UInt8) (start size offset : Nat)
    (hfit : offset + 48 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 48 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 48) :=
  bytesToNatPadded_readWindow48 memory start size offset hfit

example (memory : Nat → UInt8) (start size offset : Nat)
    (hfit : offset + 96 ≤ size) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded
        (readWindow memory start size) offset 96 =
      Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes memory (start + offset) 96) :=
  bytesToNatPadded_readWindow96 memory start size offset hfit

example (memory : Nat → UInt8) (start : Nat) (value : YulSemantics.EVM.U256) :
    Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes
          (YulSemantics.EVM.storeWord memory start value) start 32) =
      value.toNat :=
  bytesNat_readBytes_storeWord memory start value

example (memory : Nat → UInt8) (start width : Nat)
    (value : YulSemantics.EVM.U256) (hwidth : width ≤ 32) :
    Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes
          (YulSemantics.EVM.storeWord memory start value) start width) =
      value.toNat / 256 ^ (32 - width) :=
  bytesNat_readBytes_storeWord_prefix memory start width value hwidth

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesNat_readBytes_storeWord_prefix

example (memory : Nat → UInt8) (start : Nat)
    (value : YulSemantics.EVM.U256) :
    Challenge.EvmProof.Bytes.bytesNat
        (YulSemantics.EVM.readBytes
          (YulSemantics.EVM.storeByte memory start value) start 1) =
      (YulSemantics.EVM.byteAt value 0).toNat :=
  bytesNat_readBytes_storeByte memory start value

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeByte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesNat_readBytes_storeByte

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesNat_readBytes_storeWord

/-- info: 'Challenge.EvmProof.ModexpMemory.readWindow_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms readWindow_size

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow32

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow48' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow48

/-- info: 'Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow96' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatPadded_readWindow96

end Challenge.EvmProof.ModexpMemory
