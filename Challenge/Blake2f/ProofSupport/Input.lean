import Challenge.Blake2f.ProofSupport.Algorithm
import Challenge.EvmProof.Bytecode
import Mathlib.Tactic.Ring

set_option warningAsError true

/-!
# Reusable EIP-152 input and output views

These definitions factor the pinned byte-level driver into arrays of 64-bit
words. Candidate proofs can target the views without duplicating parsing and
serialization loops.
-/

namespace Challenge.Blake2f.ProofSupport.Input

open EvmSemantics

private theorem foldl_bytes (xs : List UInt8) (acc : Nat) :
    xs.foldl (fun n b => n * 256 + b.toNat) acc =
      acc * 256 ^ xs.length +
        xs.foldl (fun n b => n * 256 + b.toNat) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [ih (acc * 256 + x.toNat), ih x.toNat, Nat.pow_succ]
      ring

private theorem foldl_bytes_lt (xs : List UInt8) :
    xs.foldl (fun n b => n * 256 + b.toNat) 0 < 256 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, foldl_bytes, List.length_cons, Nat.pow_succ]
      simp only [Nat.zero_mul, Nat.zero_add]
      have hx : x.toNat < 256 := x.toNat_lt
      calc
        x.toNat * 256 ^ xs.length +
            List.foldl (fun n b => n * 256 + b.toNat) 0 xs <
            x.toNat * 256 ^ xs.length + 256 ^ xs.length :=
          Nat.add_lt_add_left ih _
        _ = (x.toNat + 1) * 256 ^ xs.length := by ring
        _ ≤ 256 * 256 ^ xs.length :=
          Nat.mul_le_mul_right (256 ^ xs.length) (by omega)
        _ = 256 ^ xs.length * 256 := by omega

theorem bytesToBigEndianNat_lt (bytes : ByteArray) :
    Data.Bytes.bytesToBigEndianNat bytes < 256 ^ bytes.size := by
  unfold Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Bytecode.toList_eq_data]
  simpa using foldl_bytes_lt bytes.data.toList

def readWords (input : ByteArray) (base count : Nat) : Array UInt64 :=
  ((List.range' 0 count).map fun i =>
    Crypto.Blake2f.readLE64 input (base + i * 8)).toArray

theorem readWords_succ (input : ByteArray) (base count : Nat) :
    readWords input base (count + 1) =
      (readWords input base count).push
        (Crypto.Blake2f.readLE64 input (base + count * 8)) := by
  simp [readWords, List.range'_1_concat]

def chaining (input : ByteArray) : Array UInt64 := readWords input 4 8

def message (input : ByteArray) : Array UInt64 := readWords input 68 16

def t0 (input : ByteArray) : UInt64 := Crypto.Blake2f.readLE64 input 196

def t1 (input : ByteArray) : UInt64 := Crypto.Blake2f.readLE64 input 204

def finalFlag (input : ByteArray) : Bool := input[212]! == 1

def writeWords (values : Array UInt64) (count : Nat) : ByteArray :=
  (List.range' 0 count).foldl
    (fun bytes i => Crypto.Blake2f.writeLE64 bytes values[i]!) ByteArray.empty

theorem writeLE64_append (bytes : ByteArray) (value : UInt64) :
    Crypto.Blake2f.writeLE64 bytes value =
      bytes ++ Crypto.Blake2f.writeLE64 ByteArray.empty value := by
  unfold Crypto.Blake2f.writeLE64
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  cases bytes with
  | mk data =>
      congr 1
      apply Array.ext'
      simp [Array.toList_push, List.append_assoc]
      rfl

@[simp] theorem writeLE64_size (bytes : ByteArray) (value : UInt64) :
    (Crypto.Blake2f.writeLE64 bytes value).size = bytes.size + 8 := by
  unfold Crypto.Blake2f.writeLE64
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl]
  norm_num [List.range', List.range.loop]

theorem writeWords_succ (values : Array UInt64) (count : Nat) :
    writeWords values (count + 1) =
      writeWords values count ++
        Crypto.Blake2f.writeLE64 ByteArray.empty values[count]! := by
  unfold writeWords
  rw [List.range'_1_concat, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [writeLE64_append]
  simp

@[simp] theorem writeWords_size (values : Array UInt64) (count : Nat) :
    (writeWords values count).size = 8 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [writeWords_succ, ByteArray.size_append, ih]
      rw [writeLE64_size]
      rw [show ByteArray.empty.size = 0 by rfl]
      omega

@[simp] theorem chaining_size (input : ByteArray) :
    (chaining input).size = 8 := by simp [chaining, readWords]

@[simp] theorem message_size (input : ByteArray) :
    (message input).size = 16 := by simp [message, readWords]

theorem compressBytes_eq (input : ByteArray) (rounds : Nat) :
    Crypto.Blake2f.compressBytes input rounds =
      writeWords
        (Crypto.Blake2f.compress rounds (chaining input) (message input)
          (t0 input) (t1 input) (finalFlag input)) 8 := by
  simp [Crypto.Blake2f.compressBytes, chaining, message, readWords,
    t0, t1, finalFlag, writeWords]

theorem compressBytes_eq_model (input : ByteArray) (rounds : Nat) :
    Crypto.Blake2f.compressBytes input rounds =
      writeWords
        (Algorithm.foldVector (chaining input)
          (Algorithm.rounds (message input) rounds
            (Algorithm.initialVector (chaining input) (t0 input) (t1 input)
              (finalFlag input)))) 8 := by
  rw [compressBytes_eq, Algorithm.compress_eq]

end Challenge.Blake2f.ProofSupport.Input
