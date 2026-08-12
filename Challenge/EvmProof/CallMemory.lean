import YulEvmCompiler.StateRel
set_option warningAsError true
/-!
# External-call return memory

The source and target call semantics use different memory representations.
This module proves their shared caller-local return-copy operation once, so
profiled precompile realizations do not duplicate byte-level reasoning.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

namespace MemMatch

/-- A byte array matches the total zero-padded view of its own byte list. -/
theorem byteFrom_toList (output : ByteArray) :
    YulEvmCompiler.MemMatch
      (YulSemantics.EVM.byteFrom output.toList) output := by
  intro address
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, ByteArray.toList_eq_data,
    Array.getElem?_toList, getElem?_def]
  split
  · rename_i haddress
    rw [Option.getD_some]
    rw [dif_pos (show address < output.size from haddress)]
    rw [ByteArray.getElem_eq_getElem_data]
    rfl
  · rename_i haddress
    rw [Option.getD_none]
    rw [dif_neg (show ¬address < output.size from haddress)]

/-- Source `copyReturn` agrees with target `State.writeReturn`, including the
empty-copy case that deliberately avoids extending target memory. -/
theorem copyReturn {ymem : Nat → UInt8} {memory : ByteArray}
    (h : YulEvmCompiler.MemMatch ymem memory) (dst size : Nat)
    (output : ByteArray) :
    YulEvmCompiler.MemMatch
      (YulSemantics.EVM.copyReturn ymem dst size output.toList)
      (State.writeReturn memory output dst size) := by
  have hlen : output.toList.length = output.size := by
    rw [ByteArray.toList_eq_data, Array.length_toList]
    rfl
  unfold State.writeReturn
  dsimp only
  split
  · rename_i hzero
    have hmin : min output.size size = 0 := by
      simpa [ByteArray.size_extract, Nat.min_comm] using hzero
    intro address
    simp only [YulSemantics.EVM.copyReturn, hlen]
    rw [if_neg (by omega)]
    exact h address
  · rename_i hnonzero
    intro address
    rw [← YulEvmCompiler.getD_eq_dite,
      MachineState.writeBytes_getElem?_getD, ByteArray.size_extract]
    simp only [Nat.sub_zero, YulSemantics.EVM.copyReturn, hlen,
      Nat.min_assoc, Nat.min_left_comm, Nat.min_self]
    by_cases hwindow : dst ≤ address ∧
        address < dst + min size output.size
    · rw [if_pos hwindow, if_pos (by simpa [Nat.min_comm] using hwindow)]
      unfold YulSemantics.EVM.byteFrom
      rw [ByteArray.toList_eq_data, List.getD_eq_getElem?_getD,
        Array.getElem?_toList]
      have hi : address - dst < output.size := by omega
      have hicopy : address - dst <
          (output.extract 0 (min output.size size)).size := by
        rw [ByteArray.size_extract]
        omega
      rw [Array.getElem?_eq_getElem hi]
      rw [getElem?_def, dif_pos hicopy, Option.getD_some]
      rw [ByteArray.getElem_extract]
      simp only [Option.getD_some, Nat.zero_add]
      rw [ByteArray.getElem_eq_getElem_data]
    · rw [if_neg hwindow, if_neg (by simpa [Nat.min_comm] using hwindow),
        YulEvmCompiler.getD_eq_dite]
      exact h address

end MemMatch

/-- Inside the copied prefix, source call-return memory is exactly the
corresponding return-data byte. -/
theorem copyReturn_inside (memory : Nat → UInt8) (dst size : Nat)
    (data : List UInt8) (i : Nat) (hsize : i < size)
    (hdata : i < data.length) :
    YulSemantics.EVM.copyReturn memory dst size data (dst + i) =
      YulSemantics.EVM.byteFrom data i := by
  unfold YulSemantics.EVM.copyReturn
  rw [if_pos]
  · simp only [Nat.add_sub_cancel_left]
  · omega

/-- A call-return copy outside a read window leaves that window unchanged. -/
theorem readBytes_copyReturn_disjoint (memory : Nat → UInt8)
    (dst size : Nat) (data : List UInt8) (start width : Nat)
    (hdisjoint : start + width ≤ dst ∨
      dst + min size data.length ≤ start) :
    YulSemantics.EVM.readBytes
        (YulSemantics.EVM.copyReturn memory dst size data) start width =
      YulSemantics.EVM.readBytes memory start width := by
  unfold YulSemantics.EVM.readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < width := by simpa using hi
  unfold YulSemantics.EVM.copyReturn
  rw [if_neg]
  rcases hdisjoint with hbefore | hafter
  · omega
  · omega

/-- A full word wholly inside a return-copy window is the corresponding
zero-padded word of the returned byte list. -/
theorem loadWord_copyReturn (memory : Nat → UInt8) (dst size : Nat)
    (data : List UInt8) (start : Nat) (hsize : start + 32 ≤ size)
    (hdata : start + 32 ≤ data.length) :
    YulSemantics.EVM.loadWord
        (YulSemantics.EVM.copyReturn memory dst size data) (dst + start) =
      YulSemantics.EVM.wordFrom data start := by
  unfold YulSemantics.EVM.loadWord YulSemantics.EVM.wordFrom
  have hfold : ∀ (indices : List Nat) (acc : BitVec 256),
      (∀ i ∈ indices, i < 32) →
      indices.foldl (fun (acc : BitVec 256) i =>
          (acc <<< (8 : Nat)) |||
            BitVec.ofNat 256
              (YulSemantics.EVM.copyReturn memory dst size data
                (dst + start + i)).toNat) acc =
        indices.foldl (fun (acc : BitVec 256) i =>
          (acc <<< (8 : Nat)) |||
            BitVec.ofNat 256
              (YulSemantics.EVM.byteFrom data (start + i)).toNat) acc := by
    intro indices
    induction indices with
    | nil => intro acc _; rfl
    | cons i rest ih =>
        intro acc hall
        rw [List.foldl_cons, List.foldl_cons]
        have hi : i < 32 := hall i (by simp)
        have hbyte :
            YulSemantics.EVM.copyReturn memory dst size data
                (dst + start + i) =
              YulSemantics.EVM.byteFrom data (start + i) := by
          rw [show dst + start + i = dst + (start + i) by omega]
          exact copyReturn_inside memory dst size data (start + i)
            (by omega) (by omega)
        rw [hbyte]
        exact ih _ (fun j hj => hall j (by simp [hj]))
  exact hfold (List.range 32) 0 (by
    intro i hi
    simpa using hi)

end Challenge.EvmProof
