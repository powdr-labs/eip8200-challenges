import Batteries.Data.ByteArray
import Init.Omega

set_option warningAsError true

/-!
# Byte-list bridges for source-Yul specifications

Pure conversions between core's tail-recursive `ByteArray.toList` and the
array/list representations used at Yul semantic boundaries.
-/

namespace Challenge.YulProof.Bytes

private theorem get!_eq (bytes : Array UInt8) (i : Nat)
    (hi : i < bytes.toList.length) :
    ByteArray.get! ⟨bytes⟩ i = bytes.toList[i] := by
  show bytes[i]! = _
  have hib : i < bytes.size := by simpa using hi
  rw [getElem!_pos bytes i hib]
  exact (Array.getElem_toList hib).symm

private theorem toList_loop_eq (bytes : Array UInt8) :
    ∀ n i acc, bytes.size - i ≤ n →
      ByteArray.toList.loop ⟨bytes⟩ i acc =
        acc.reverse ++ bytes.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i acc h
    unfold ByteArray.toList.loop
    rw [if_neg (by show ¬i < bytes.size; omega)]
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]
    rw [List.append_nil]
  | succ n ih =>
    intro i acc h
    unfold ByteArray.toList.loop
    by_cases hi : (⟨bytes⟩ : ByteArray).size > i
    · rw [if_pos hi]
      rw [ih (i + 1) _ (by
        show bytes.size - (i + 1) ≤ n
        have : bytes.size > i := hi
        omega)]
      have hi' : i < bytes.toList.length := by
        rw [Array.length_toList]
        exact hi
      rw [List.drop_eq_getElem_cons hi', get!_eq bytes i hi']
      simp
    · rw [if_neg hi]
      have hle : bytes.toList.length ≤ i := by
        rw [Array.length_toList]
        exact Nat.le_of_not_lt hi
      rw [List.drop_eq_nil_of_le hle, List.append_nil]

theorem toList_eq_data (input : ByteArray) :
    input.toList = input.data.toList := by
  obtain ⟨bytes⟩ := input
  show ByteArray.toList.loop ⟨bytes⟩ 0 [] = _
  rw [toList_loop_eq bytes bytes.size 0 [] (by omega)]
  simp

@[simp] theorem ofList_toList (bytes : List UInt8) :
    (ByteArray.mk bytes.toArray).toList = bytes := by
  rw [toList_eq_data]

@[simp] theorem ofToList (input : ByteArray) :
    ByteArray.mk input.toList.toArray = input := by
  apply ByteArray.ext
  rw [toList_eq_data]

end Challenge.YulProof.Bytes
