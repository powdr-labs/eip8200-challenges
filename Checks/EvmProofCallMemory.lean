import Challenge.EvmProof.CallMemory
set_option warningAsError true
/-!
# External-call return-memory checks
-/

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

example {ymem : Nat → UInt8} {memory output : ByteArray}
    (h : MemMatch ymem memory) (dst size : Nat) :
    MemMatch (YulSemantics.EVM.copyReturn ymem dst size output.toList)
      (State.writeReturn memory output dst size) :=
  Challenge.EvmProof.MemMatch.copyReturn h dst size output

example (output : ByteArray) :
    MemMatch (YulSemantics.EVM.byteFrom output.toList) output :=
  Challenge.EvmProof.MemMatch.byteFrom_toList output

example (memory : Nat → UInt8) (dst size : Nat) (data : List UInt8)
    (start : Nat) (hsize : start + 32 ≤ size)
    (hdata : start + 32 ≤ data.length) :
    YulSemantics.EVM.loadWord
        (YulSemantics.EVM.copyReturn memory dst size data) (dst + start) =
      YulSemantics.EVM.wordFrom data start :=
  Challenge.EvmProof.loadWord_copyReturn memory dst size data start hsize hdata

example (memory : Nat → UInt8) (dst size : Nat) (data : List UInt8)
    (start width : Nat)
    (hdisjoint : start + width ≤ dst ∨
      dst + min size data.length ≤ start) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.copyReturn memory dst size data) start width =
      YulSemantics.EVM.readBytes memory start width :=
  Challenge.EvmProof.readBytes_copyReturn_disjoint
    memory dst size data start width hdisjoint

/-- info: 'Challenge.EvmProof.copyReturn_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.copyReturn_inside

/-- info: 'Challenge.EvmProof.loadWord_copyReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.loadWord_copyReturn

/-- info: 'Challenge.EvmProof.readBytes_copyReturn_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.readBytes_copyReturn_disjoint

/-- info: 'Challenge.EvmProof.MemMatch.copyReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.MemMatch.copyReturn

/-- info: 'Challenge.EvmProof.MemMatch.byteFrom_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.MemMatch.byteFrom_toList
