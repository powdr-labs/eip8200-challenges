import Challenge.EvmProof.ByteWindow

set_option warningAsError true

namespace Checks.EvmProofByteWindow

open EvmSemantics

example (pre window suffix : ByteArray) :
    (pre ++ window ++ suffix).extract pre.size
        (pre.size + window.size) = window :=
  Challenge.EvmProof.ByteWindow.extract_append_window pre window suffix

example (pre window suffix : ByteArray) :
    Data.Bytes.bytesToBigEndianNat
        ((pre ++ window ++ suffix).extract pre.size
          (pre.size + window.size)) =
      Data.Bytes.bytesToBigEndianNat window :=
  Challenge.EvmProof.ByteWindow.bytesToBigEndianNat_extract_append
    pre window suffix

example (n prefixWidth valueWidth : Nat) (h : n < 256 ^ valueWidth) :
    Data.Bytes.natToBytesPadded n (prefixWidth + valueWidth) =
      ByteArray.mk (Array.replicate prefixWidth 0) ++
        Data.Bytes.natToBytesPadded n valueWidth :=
  Challenge.EvmProof.ByteWindow.natToBytesPadded_prefix_zeros
    n prefixWidth valueWidth h

example (bytes : ByteArray) :
    Data.Bytes.natToBytesPadded (Data.Bytes.bytesToBigEndianNat bytes)
        bytes.size = bytes :=
  Challenge.EvmProof.ByteWindow.natToBytesPadded_bytesToBigEndianNat bytes

example (bytes : ByteArray) (offset width : Nat)
    (hfit : offset + width ≤ bytes.size) :
    EvmSemantics.MachineState.readPadded bytes offset width =
      bytes.extract offset (offset + width) :=
  Challenge.EvmProof.Bytes.readPadded_eq_extract bytes offset width hfit

/-- info: 'Challenge.EvmProof.Bytes.bytesNat_injective_of_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytes.bytesNat_injective_of_length

/-- info: 'Challenge.EvmProof.Bytes.readPadded_eq_extract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytes.readPadded_eq_extract

/--
info: 'Challenge.EvmProof.ByteWindow.natToBytesPadded_bytesToBigEndianNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.EvmProof.ByteWindow.natToBytesPadded_bytesToBigEndianNat

/-- info: 'Challenge.EvmProof.ByteWindow.extract_append_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.ByteWindow.extract_append_window

/--
info: 'Challenge.EvmProof.ByteWindow.bytesToBigEndianNat_extract_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.EvmProof.ByteWindow.bytesToBigEndianNat_extract_append

/-- info: 'Challenge.EvmProof.ByteWindow.natToBytesPadded_prefix_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.ByteWindow.natToBytesPadded_prefix_zeros

end Checks.EvmProofByteWindow
