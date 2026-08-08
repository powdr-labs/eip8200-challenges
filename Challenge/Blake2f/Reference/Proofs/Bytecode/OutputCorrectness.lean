import Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitializationCorrectness
import Challenge.Blake2f.Reference.Proofs.Bytecode.StoreLE64Correctness
import Challenge.Blake2f.Reference.Proofs.Bytecode.OutputGas

set_option warningAsError true
set_option maxHeartbeats 1000000

/-! Functional refinement of the compiled fold and serialization loop. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.OutputCorrectness

open Challenge.Blake2f
open Challenge.Blake2f.ProofSupport
open EvmSemantics

private theorem xor_eq (x y : UInt256) : UInt256.xor x y = x ^^^ y := rfl

theorem rounds_lt (input : ByteArray) : rounds input < 2 ^ 256 := by
  have hread := Input.bytesToBigEndianNat_lt (input.extract 0 4)
  have hsize : (input.extract 0 4).size ≤ 4 := by simp
  calc
    rounds input < 256 ^ (input.extract 0 4).size := hread
    _ ≤ 256 ^ 4 := Nat.pow_le_pow_right (by omega) hsize
    _ < 2 ^ 256 := by norm_num

private theorem representsAt_roundTransition_before {memory : ByteArray}
    {values : Array UInt64} {base : Nat} (round : Nat)
    (represents : Memory.RepresentsAt memory base values)
    (hbefore : base + 32 * values.size ≤ 768)
    (hfits : base + 32 * values.size < 2 ^ 256) :
    Memory.RepresentsAt (Round.transition memory round) base values := by
  have before (address : Nat) (haddress : 768 ≤ address)
      (hsmall : address < 2 ^ 256) :
      base + 32 * values.size ≤ (UInt256.ofNat address).toNat := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hsmall]
    omega
  have rep1 := MixGCorrectness.representsAt_transition_before memory values base
    768 896 1024 1152 (UInt256.ofNat round) 0 1 represents hfits
    (before 768 (by omega) (by norm_num)) (before 896 (by omega) (by norm_num))
    (before 1024 (by omega) (by norm_num)) (before 1152 (by omega) (by norm_num))
  have rep2 := MixGCorrectness.representsAt_transition_before
    (Round.memory1 memory round) values base
    800 928 1056 1184 (UInt256.ofNat round) 2 3 rep1 hfits
    (before 800 (by omega) (by norm_num)) (before 928 (by omega) (by norm_num))
    (before 1056 (by omega) (by norm_num)) (before 1184 (by omega) (by norm_num))
  have rep3 := MixGCorrectness.representsAt_transition_before
    (Round.memory2 memory round) values base
    832 960 1088 1216 (UInt256.ofNat round) 4 5 rep2 hfits
    (before 832 (by omega) (by norm_num)) (before 960 (by omega) (by norm_num))
    (before 1088 (by omega) (by norm_num)) (before 1216 (by omega) (by norm_num))
  have rep4 := MixGCorrectness.representsAt_transition_before
    (Round.memory3 memory round) values base
    864 992 1120 1248 (UInt256.ofNat round) 6 7 rep3 hfits
    (before 864 (by omega) (by norm_num)) (before 992 (by omega) (by norm_num))
    (before 1120 (by omega) (by norm_num)) (before 1248 (by omega) (by norm_num))
  have rep5 := MixGCorrectness.representsAt_transition_before
    (Round.memory4 memory round) values base
    768 928 1088 1248 (UInt256.ofNat round) 8 9 rep4 hfits
    (before 768 (by omega) (by norm_num)) (before 928 (by omega) (by norm_num))
    (before 1088 (by omega) (by norm_num)) (before 1248 (by omega) (by norm_num))
  have rep6 := MixGCorrectness.representsAt_transition_before
    (Round.memory5 memory round) values base
    800 960 1120 1152 (UInt256.ofNat round) 10 11 rep5 hfits
    (before 800 (by omega) (by norm_num)) (before 960 (by omega) (by norm_num))
    (before 1120 (by omega) (by norm_num)) (before 1152 (by omega) (by norm_num))
  have rep7 := MixGCorrectness.representsAt_transition_before
    (Round.memory6 memory round) values base
    832 992 1024 1184 (UInt256.ofNat round) 12 13 rep6 hfits
    (before 832 (by omega) (by norm_num)) (before 992 (by omega) (by norm_num))
    (before 1024 (by omega) (by norm_num)) (before 1184 (by omega) (by norm_num))
  have rep8 := MixGCorrectness.representsAt_transition_before
    (Round.memory7 memory round) values base
    864 896 1056 1216 (UInt256.ofNat round) 14 15 rep7 hfits
    (before 864 (by omega) (by norm_num)) (before 896 (by omega) (by norm_num))
    (before 1056 (by omega) (by norm_num)) (before 1216 (by omega) (by norm_num))
  simpa [Round.transition, Round.memory8] using rep8

theorem representsAt_roundMemories_before {memory : ByteArray}
    {values : Array UInt64} {base : Nat} (count : Nat)
    (represents : Memory.RepresentsAt memory base values)
    (hbefore : base + 32 * values.size ≤ 768)
    (hfits : base + 32 * values.size < 2 ^ 256) :
    Memory.RepresentsAt (Round.memories memory count) base values := by
  induction count with
  | zero => simpa [Round.memories] using represents
  | succ count ih =>
      rw [Round.memories]
      exact representsAt_roundTransition_before count ih hbefore hfits

theorem readWord_writtenMemory_before (memory : ByteArray) (address : Nat)
    (value : UInt256) (count offset : Nat) (hcount : count ≤ 8)
    (hbefore : offset + 32 ≤ address) :
    MachineState.readWord
        (StoreLE64.writtenMemory memory address value count) offset =
      MachineState.readWord memory offset := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [StoreLE64.writtenMemory, StoreLE64.writeByte]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · left
        omega

theorem readWord_outputMemory_before (initial : ByteArray) (count offset : Nat)
    (hcount : count ≤ 8) (hbefore : offset + 32 ≤ 1280) :
    MachineState.readWord (Output.outputMemory initial count) offset =
      MachineState.readWord initial offset := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Output.outputMemory]
      rw [readWord_writtenMemory_before _ _ _ 8 offset (by omega) (by omega)]
      exact ih (by omega)

theorem outputWord_eq {initial : ByteArray} {h vector : Array UInt64}
    (count i : Nat) (hcount : count ≤ 8) (hi : i < 8)
    (hrep : Memory.RepresentsAt initial 0 h)
    (vrep : Memory.RepresentsAt initial 768 vector)
    (hhsize : h.size = 8) (hvsize : vector.size = 16) :
    Output.outputWord (Output.outputMemory initial count) i =
      Word.ofUInt64 (Algorithm.foldVector h vector)[i]! := by
  unfold Output.outputWord
  rw [readWord_outputMemory_before initial count (32 * i) hcount (by omega),
    readWord_outputMemory_before initial count (768 + 32 * i) hcount (by omega),
    readWord_outputMemory_before initial count (1024 + 32 * i) hcount (by omega)]
  have rh := hrep i (by omega)
  have rv := vrep i (by omega)
  have rv8 := vrep (i + 8) (by omega)
  simp only [Nat.zero_add] at rh
  rw [rh, rv, show 1024 + 32 * i = 768 + 32 * (i + 8) by omega, rv8]
  rw [xor_eq, xor_eq, ← Word.ofUInt64_xor, ← Word.ofUInt64_xor]
  congr 1
  exact (Algorithm.foldVector_getElem! h vector i hi).symm

theorem outputMemory_eq_writeWords {initial : ByteArray}
    {h vector : Array UInt64} (count : Nat) (hcount : count ≤ 8)
    (hrep : Memory.RepresentsAt initial 0 h)
    (vrep : Memory.RepresentsAt initial 768 vector)
    (hhsize : h.size = 8) (hvsize : vector.size = 16) :
    Output.outputMemory initial count =
      MachineState.writeBytes initial
        (Input.writeWords (Algorithm.foldVector h vector) count) 1280 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Output.outputMemory,
        StoreLE64Correctness.writtenMemory_eight,
        outputWord_eq count count (by omega) (by omega) hrep vrep hhsize hvsize,
        StoreLE64Correctness.wordBytes_ofUInt64,
        ih (by omega), Input.writeWords_succ]
      rw [show 1280 + 8 * count =
          1280 + (Input.writeWords (Algorithm.foldVector h vector) count).size by
        rw [Input.writeWords_size]]
      rw [Challenge.EvmProof.Memory.writeBytes_append_adjacent]

theorem readOutput_eq {initial : ByteArray} {h vector : Array UInt64}
    (hrep : Memory.RepresentsAt initial 0 h)
    (vrep : Memory.RepresentsAt initial 768 vector)
    (hhsize : h.size = 8) (hvsize : vector.size = 16) :
    MachineState.readPadded (Output.outputMemory initial 8) 1280 64 =
      Input.writeWords (Algorithm.foldVector h vector) 8 := by
  rw [outputMemory_eq_writeWords 8 (by omega) hrep vrep hhsize hvsize]
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same initial
    (Input.writeWords (Algorithm.foldVector h vector) 8) 1280
  simpa using hread

theorem finalState_return_eq_spec (s : EVM.State) (input : ByteArray)
    (hflag : input[212]!.toNat ≤ 1) :
    (Output.finalState s
      (Round.memories (ScalarInitialization.finalMemory input) (rounds input))
      (Prelude.roundsWord input) (Prelude.finalFlagWord input)).hReturn =
      spec input := by
  have hrounds := rounds_lt input
  have initialModel := ScalarInitializationCorrectness.finalMemory_model input hflag
  have model := RoundCorrectness.memoryModel_memories (rounds input) hrounds
    (Input.message_size input) (Algorithm.initialVector_size _ _ _ _)
    initialModel
  have hrep := representsAt_roundMemories_before (rounds input)
    (ScalarInitializationCorrectness.finalMemory_represents_h input)
    (by simp) (by simp)
  change MachineState.readPadded
      (Output.outputMemory
        (Round.memories (ScalarInitialization.finalMemory input) (rounds input)) 8)
      1280 64 = spec input
  rw [readOutput_eq hrep model.vector (Input.chaining_size input)
    (by
      rw [Algorithm.rounds_size, Algorithm.initialVector_size])]
  rw [spec, Input.compressBytes_eq_model]

end Challenge.Blake2f.Reference.Proofs.Bytecode.OutputCorrectness
