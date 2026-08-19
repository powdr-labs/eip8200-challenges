import Challenge.Sha256.Submissions.Sha256Fast.Proofs.EndToEndTrace

set_option warningAsError false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailMemoryBridge

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Word
open DriverLoop TailState

namespace Ref

abbrev canonicalTail :=
  Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail
abbrev canonicalTail_eq :=
  Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail_eq
abbrev zeroCount_eq :=
  Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.zeroCount_eq
abbrev zeroBytes :=
  Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroBytes
abbrev zeroBytes_size :=
  Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroBytes_size
abbrev lengthBytes :=
  Challenge.Sha256.Reference.Proofs.Bytecode.Padding.lengthBytes
abbrev lengthBytes_size :=
  Challenge.Sha256.Reference.Proofs.Bytecode.Padding.lengthBytes_size

end Ref

def tailOffset (input : ByteArray) : Nat := input.size / 64 * 64
def remainder (input : ByteArray) : Nat := input.size % 64

theorem tailOffset_add_remainder (input : ByteArray) :
    tailOffset input + remainder input = input.size := by
  unfold tailOffset remainder
  have := Nat.div_add_mod' input.size 64
  omega

theorem tailOffset_le (input : ByteArray) : tailOffset input ≤ input.size := by
  have := tailOffset_add_remainder input
  omega

theorem tailExtract_size (input : ByteArray) :
    (input.extract (tailOffset input) input.size).size = remainder input := by
  rw [ByteArray.size_extract]
  simp only [Nat.min_self]
  have h := tailOffset_add_remainder input
  omega

theorem canonicalTail_size_short (input : ByteArray)
    (hshort : remainder input < 56) : (Ref.canonicalTail input).size = 64 := by
  change (Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail input).size = 64
  rw [Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail_eq]
  have htail : (input.extract (input.size / 64 * 64) input.size).size =
      input.size % 64 := by simpa [tailOffset, remainder] using tailExtract_size input
  simp only [ByteArray.size_append, Ref.zeroBytes_size,
    Ref.lengthBytes_size, show (ByteArray.mk #[0x80]).size = 1 by rfl]
  rw [htail]
  rw [Ref.zeroCount_eq]
  have hshort' : input.size % 64 < 56 := by simpa [remainder] using hshort
  rw [if_pos hshort']
  omega

theorem canonicalTail_size_long (input : ByteArray)
    (hlong : ¬ remainder input < 56) : (Ref.canonicalTail input).size = 128 := by
  change (Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail input).size = 128
  rw [Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail_eq]
  have htail : (input.extract (input.size / 64 * 64) input.size).size =
      input.size % 64 := by simpa [tailOffset, remainder] using tailExtract_size input
  simp only [ByteArray.size_append, Ref.zeroBytes_size,
    Ref.lengthBytes_size, show (ByteArray.mk #[0x80]).size = 1 by rfl]
  rw [htail]
  rw [Ref.zeroCount_eq]
  have hlong' : ¬ input.size % 64 < 56 := by simpa [remainder] using hlong
  rw [if_neg hlong']
  have hr := Nat.mod_lt input.size (by omega : 0 < 64)
  omega

def lengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.land (UInt256.ofNat 18446744073709551615)
      (UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)))
    (UInt256.ofNat 192)

theorem lengthWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    lengthWord input = UInt256.ofNat
      ((input.size * 8 % 2 ^ 64) * 2 ^ 192) := by
  unfold lengthWord
  unfold CalldataFits at hfit
  rw [shiftLeft_ofNat (Nat.lt_trans hfit (by norm_num)) (by omega) (by
    calc
      input.size * 2 ^ 3 < 2 ^ 64 * 2 ^ 3 :=
        Nat.mul_lt_mul_of_pos_right hfit (by positivity)
      _ = 2 ^ 67 := by norm_num
      _ < 2 ^ 256 := by norm_num)]
  have hmask : UInt256.land (UInt256.ofNat 18446744073709551615)
      (UInt256.ofNat (input.size * 2 ^ 3)) =
      UInt256.ofNat (input.size * 8 % 2 ^ 64) := by
    apply word_ext
    rw [word_toNat_land, word_toNat_ofNat, word_toNat_ofNat,
      word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by norm_num : 18446744073709551615 < 2 ^ 256),
      Nat.mod_eq_of_lt (by
        calc
          input.size * 2 ^ 3 < 2 ^ 64 * 2 ^ 3 :=
            Nat.mul_lt_mul_of_pos_right hfit (by positivity)
          _ < 2 ^ 256 := by norm_num),
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by positivity))
        (by norm_num : 2 ^ 64 < 2 ^ 256))]
    rw [show 18446744073709551615 = 2 ^ 64 - 1 by norm_num,
      Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    norm_num
  rw [hmask]
  apply shiftLeft_ofNat
  · exact Nat.lt_trans (Nat.mod_lt _ (by positivity)) (by norm_num)
  · omega
  · calc
      (input.size * 8 % 2 ^ 64) * 2 ^ 192 < 2 ^ 64 * 2 ^ 192 :=
        Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by positivity)) (by positivity)
      _ = 2 ^ 256 := by rw [← Nat.pow_add]

private theorem div_mod_of_mod_of_dvd (n modulus d base : Nat)
    (hdvd : d * base ∣ modulus) :
    (n % modulus) / d % base = n / d % base := by
  calc
    (n % modulus) / d % base =
        (n % modulus) % (d * base) / d :=
      (Nat.mod_mul_right_div_self (n % modulus) d base).symm
    _ = n % (d * base) / d :=
      congrArg (fun x : Nat => x / d) (Nat.mod_mod_of_dvd n hdvd)
    _ = n / d % base := Nat.mod_mul_right_div_self n d base

private theorem byte_of_mod_256_pow_eight (n i : Nat) (hi : i < 8) :
    (n % 256 ^ 8) / 256 ^ (8 - 1 - i) % 256 =
      n / 256 ^ (8 - 1 - i) % 256 := by
  let d := 256 ^ (8 - 1 - i)
  have hd : d * 256 = 256 ^ (8 - i) := by
    dsimp [d]
    rw [← Nat.pow_succ]
    congr 2
    omega
  have hdvd : d * 256 ∣ 256 ^ 8 := by
    rw [hd]
    exact Nat.pow_dvd_pow 256 (by omega)
  exact div_mod_of_mod_of_dvd n (256 ^ 8) d 256 hdvd

theorem lengthBytes32_prefix (input : ByteArray) (hfit : CalldataFits input) :
    MachineState.readPadded
      (Data.Bytes.natToBytesPadded (lengthWord input).toNat 32) 0 8 =
      Ref.lengthBytes input := by
  have hw := congrArg UInt256.toNat (lengthWord_eq input hfit)
  rw [word_toNat_ofNat, Nat.mod_eq_of_lt (by
    calc
      (input.size * 8 % 2 ^ 64) * 2 ^ 192 < 2 ^ 64 * 2 ^ 192 :=
        Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by positivity)) (by positivity)
      _ = 2 ^ 256 := by rw [← Nat.pow_add])] at hw
  let low := input.size * 8 % 256 ^ 8
  have hword : (lengthWord input).toNat = low * 256 ^ 24 := by
    rw [hw]
    simp only [low]
    rw [show 2 ^ 64 = 256 ^ 8 by norm_num [pow_mul],
      show 2 ^ 192 = 256 ^ 24 by norm_num [pow_mul]]
  have hsplit : Data.Bytes.natToBytesPadded (low * 256 ^ 24) 32 =
      Data.Bytes.natToBytesPadded low 8 ++
        Data.Bytes.natToBytesPadded 0 24 := by
    simpa using
      (Challenge.Sha256.Reference.Proofs.Bytecode.DriverCorrect.natToBytesPadded_concat
        low 0 8 24 (by positivity))
  have hprefix : MachineState.readPadded
      (Data.Bytes.natToBytesPadded low 8 ++
        Data.Bytes.natToBytesPadded 0 24) 0 8 =
      Data.Bytes.natToBytesPadded low 8 := by
    apply ByteArray.ext_getElem
    · rw [Challenge.EvmProof.Memory.readPadded_size,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    · intro i hleft hright
      have hi : i < 8 := by
        simpa [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
        ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
      simp only [Nat.zero_add]
      rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by simpa)]
  rw [hword, hsplit, hprefix]
  unfold Ref.lengthBytes Challenge.Sha256.Reference.Proofs.Bytecode.Padding.lengthBytes
  apply ByteArray.ext_getElem
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hleft hright
    have hi : i < 8 := by
      simpa [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD low 8 i hi,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
        (input.size * 8) 8 i hi]
    apply congrArg UInt8.ofNat
    exact byte_of_mod_256_pow_eight (input.size * 8) i hi

def firstPaddedBlock (input : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (MachineState.readPadded input (tailOffset input) 64)
    (ByteArray.mk #[0x80]) (remainder input)

def shortPaddedBlock (input : ByteArray) : ByteArray :=
  MachineState.writeBytes (firstPaddedBlock input) (Ref.lengthBytes input) 56

def lastPaddedBlock (input : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (Data.Bytes.natToBytesPadded 0 64) (Ref.lengthBytes input) 56

@[simp] theorem firstPaddedBlock_size (input : ByteArray) :
    (firstPaddedBlock input).size = 64 := by
  unfold firstPaddedBlock
  rw [MachineState.writeBytes_size]
  simp only [show (ByteArray.mk #[0x80]).size = 1 by rfl, one_ne_zero,
    if_false, Challenge.EvmProof.Memory.readPadded_size]
  have hr := Nat.mod_lt input.size (by omega : 0 < 64)
  simp only [remainder]
  omega

@[simp] theorem shortPaddedBlock_size (input : ByteArray) :
    (shortPaddedBlock input).size = 64 := by
  unfold shortPaddedBlock
  rw [MachineState.writeBytes_size, Ref.lengthBytes_size]
  simp

@[simp] theorem lastPaddedBlock_size (input : ByteArray) :
    (lastPaddedBlock input).size = 64 := by
  unfold lastPaddedBlock
  rw [MachineState.writeBytes_size, Ref.lengthBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  simp

theorem endWord_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (endWord input).toNat = tailOffset input := by
  simpa [endWord, blockCount, tailOffset] using
    DriverLoop.offsetWord_toNat input hfit (blockCount input) (by omega)

theorem sizeWord_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (sizeWord input).toNat = input.size := by
  unfold sizeWord CalldataFits at *
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans hfit (by norm_num)

theorem prepared_window (s : State) (input : ByteArray)
    (endW : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hcalldata : s.executionEnv.calldata = input) :
    MachineState.readPadded
      (prepared s (endWord input) endW (remWord input)
        (sizeWord input) rest).memory 288 64 =
      firstPaddedBlock input := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < 64 := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
    unfold prepared firstPaddedBlock
    rw [MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD]
    rw [endWord_toNat input hfit, hcalldata]
    have hsentOff : (UInt256.ofNat 288 + remWord input).toNat =
        288 + input.size % 64 := by
      rw [Challenge.EvmProof.Word.word_toNat_add,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        EndToEndTrace.remWord_toNat,
        Nat.mod_eq_of_lt (by norm_num : 288 < 2 ^ 256),
        Nat.mod_eq_of_lt]
      have hr := Nat.mod_lt input.size (by omega : 0 < 64)
      omega
    rw [hsentOff]
    have honeOfNat : (ByteArray.mk #[UInt8.ofNat 128]).size = 1 := rfl
    have honeHex : (ByteArray.mk #[0x80]).size = 1 := rfl
    rw [honeOfNat, honeHex, Challenge.EvmProof.Memory.readPadded_size]
    have hr := Nat.mod_lt input.size (by omega : 0 < 64)
    by_cases hsentinel : i = remainder input
    · subst i
      simp [remainder, hi]
    · have hcL : ¬(288 + input.size % 64 ≤ 288 + i ∧
          288 + i < 288 + input.size % 64 + 1) := by
        simp only [remainder] at hsentinel
        omega
      have hcR : ¬(remainder input ≤ i ∧
          i < remainder input + 1) := by omega
      have hb : 288 ≤ 288 + i ∧ 288 + i < 288 + 64 := by omega
      rw [if_neg hcL, if_pos hb, if_neg hcR]
      simp

theorem lengthEntry_window (s : State) (input : ByteArray)
    (off endW rem : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input) :
    MachineState.readPadded
      (lengthEntry s off endW rem (sizeWord input) rest).memory 288 64 =
      MachineState.writeBytes
        (MachineState.readPadded s.memory 288 64)
        (Ref.lengthBytes input) 56 := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size,
      MachineState.writeBytes_size, Ref.lengthBytes_size]
    simp
  · intro i hleft hright
    have hi : i < 64 := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
    unfold lengthEntry sizeWord
    rw [MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD]
    rw [show (Data.Bytes.natToBytesPadded
        (UInt256.shiftLeft
          (UInt256.land (UInt256.ofNat 18446744073709551615)
            (UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)))
          (UInt256.ofNat 192)).toNat 32).size = 32 by
      exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _]
    rw [Ref.lengthBytes_size]
    by_cases hfooter : 56 ≤ i
    · have hleftCond : 344 ≤ 288 + i ∧ 288 + i < 344 + 32 := by omega
      have hrightCond : 56 ≤ i ∧ i < 56 + 8 := by omega
      rw [if_pos hleftCond, if_pos hrightCond]
      have hp := congrArg (fun bytes : ByteArray =>
          (bytes[i - 56]?.getD 0)) (lengthBytes32_prefix input hfit)
      rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD,
        if_pos (by omega)] at hp
      have hidx : 288 + i - 344 = i - 56 := by omega
      rw [hidx]
      simpa [lengthWord] using hp
    · have hleftCond : ¬(344 ≤ 288 + i ∧ 288 + i < 344 + 32) := by omega
      have hrightCond : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
      rw [if_neg hleftCond, if_neg hrightCond,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]

theorem cleared_window (s : State) (H : Array UInt32)
    (off endW rem n : UInt256) (rest : List UInt256) :
    MachineState.readPadded
      (cleared s H off endW rem n rest).memory 288 64 =
      Data.Bytes.natToBytesPadded 0 64 := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hleft hright
    have hi : i < 64 := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
    unfold cleared
    rw [MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD 0 64 i hi]
    by_cases hfirst : i < 32
    · have hlastCond : ¬(320 ≤ 288 + i ∧
          288 + i < 320 + (Data.Bytes.natToBytesPadded 0 32).size) := by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega
      have hfirstCond : 288 ≤ 288 + i ∧
          288 + i < 288 + (Data.Bytes.natToBytesPadded 0 32).size := by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega
      rw [if_neg hlastCond, if_pos hfirstCond]
      have hidx : 288 + i - 288 = i := by omega
      rw [hidx,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
          0 32 i hfirst]
      simp
    · have hlastCond : 320 ≤ 288 + i ∧
          288 + i < 320 + (Data.Bytes.natToBytesPadded 0 32).size := by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega
      rw [if_pos hlastCond,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
          0 32 (288 + i - 320) (by omega)]
      simp

theorem short_candidate_window (s : State) (input : ByteArray)
    (endW : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hcalldata : s.executionEnv.calldata = input) :
    MachineState.readPadded
      (lengthEntry
        (shortBranch s (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (endWord input) endW (remWord input) (sizeWord input) rest).memory
      288 64 = shortPaddedBlock input := by
  rw [lengthEntry_window _ input _ _ _ _ hfit]
  have hp := prepared_window s input endW rest hfit hcalldata
  simpa [shortBranch, shortPaddedBlock] using congrArg
    (fun b : ByteArray => MachineState.writeBytes b (Ref.lengthBytes input) 56) hp

theorem long_last_candidate_window (s : State) (input : ByteArray)
    (H : Array UInt32) (endW : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input) :
    MachineState.readPadded
      (lengthEntry
        (cleared s H (endWord input) endW (remWord input)
          (sizeWord input) rest)
        (endWord input) endW (remWord input) (sizeWord input) rest).memory
      288 64 = lastPaddedBlock input := by
  rw [lengthEntry_window _ input _ _ _ _ hfit]
  have hc := cleared_window s H (endWord input) endW (remWord input)
    (sizeWord input) rest
  simpa [lastPaddedBlock] using congrArg
    (fun b : ByteArray => MachineState.writeBytes b (Ref.lengthBytes input) 56) hc

theorem tailExtract_getD (input : ByteArray) (i : Nat)
    (hi : i < remainder input) :
    (input.extract (tailOffset input) input.size)[i]?.getD 0 =
      input[tailOffset input + i]?.getD 0 := by
  have htailSize := tailExtract_size input
  have hsource : tailOffset input + i < input.size := by
    have hadd := tailOffset_add_remainder input
    omega
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem!,
    getElem!_pos _ i (by simpa [htailSize] using hi),
    ByteArray.getElem_extract]
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem!,
    getElem!_pos input (tailOffset input + i) hsource]

theorem zeroBytes_getD (input : ByteArray) (i : Nat)
    (hi : i < Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount
      input.size) :
    (Ref.zeroBytes input.size)[i]?.getD 0 = 0 := by
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem!]
  rw [getElem!_pos _ i (by simpa using hi)]
  have harray : i < (Array.replicate
      (Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount input.size)
      (0 : UInt8)).size := by simpa using hi
  change (Array.replicate
    (Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount input.size)
    (0 : UInt8))[i]'harray = 0
  exact Array.getElem_replicate harray

theorem canonicalTail_getD (input : ByteArray) (i : Nat) :
    (Ref.canonicalTail input)[i]?.getD 0 =
      if i < remainder input then
        input[tailOffset input + i]?.getD 0
      else if i = remainder input then 0x80
      else if i < remainder input + 1 +
          Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount input.size then
        0
      else
        (Ref.lengthBytes input)[i - (remainder input + 1 +
          Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount input.size)]?.getD 0 := by
  change (Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail
    input)[i]?.getD 0 = _
  rw [Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge.canonicalTail_eq]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append,
    Challenge.EvmProof.Memory.getElem?_getD_append,
    Challenge.EvmProof.Memory.getElem?_getD_append]
  simp only [ByteArray.size_append]
  have htailSize : (input.extract (input.size / 64 * 64) input.size).size =
      remainder input := by simpa [tailOffset] using tailExtract_size input
  rw [htailSize, Ref.zeroBytes_size]
  have hone : (ByteArray.mk #[0x80]).size = 1 := rfl
  rw [hone]
  by_cases htail : i < remainder input
  · have hpair : i < remainder input + 1 := by omega
    have htriple : i < remainder input + 1 +
        Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount input.size := by
      omega
    rw [if_pos htriple, if_pos hpair, if_pos htail, if_pos htail]
    simpa [tailOffset] using tailExtract_getD input i htail
  · by_cases hsentinel : i = remainder input
    · subst i
      have hpair : remainder input < remainder input + 1 := by omega
      have htriple : remainder input < remainder input + 1 +
          Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount input.size := by
        omega
      rw [if_pos htriple, if_pos hpair, if_neg (by omega),
        if_neg (by omega), if_pos rfl]
      simp only [Nat.sub_self]
      rw [Challenge.EvmProof.Memory.getD0_eq_getElem!,
        getElem!_pos _ 0 (by omega)]
      rfl
    · have hafter : remainder input + 1 ≤ i := by omega
      by_cases hzero : i < remainder input + 1 +
          Challenge.Sha256.Reference.Proofs.Bytecode.Padding.zeroCount input.size
      · rw [if_pos hzero, if_neg (by omega), if_neg htail,
          if_neg hsentinel, if_pos hzero]
        exact zeroBytes_getD input (i - (remainder input + 1)) (by omega)
      · rw [if_neg hzero, if_neg htail, if_neg hsentinel, if_neg hzero]

theorem firstPaddedBlock_eq_canonical_first (input : ByteArray)
    (hlong : ¬ remainder input < 56) :
    firstPaddedBlock input =
      MachineState.readPadded (Ref.canonicalTail input) 0 64 := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < 64 := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
    simp only [Nat.zero_add]
    rw [canonicalTail_getD]
    unfold firstPaddedBlock
    rw [MachineState.writeBytes_getElem?_getD]
    have hone : (ByteArray.mk #[0x80]).size = 1 := rfl
    rw [hone]
    rw [Ref.zeroCount_eq]
    have hlongMod : ¬ input.size % 64 < 56 := by
      simpa [remainder] using hlong
    simp only [if_neg hlongMod]
    have hr := Nat.mod_lt input.size (by omega : 0 < 64)
    by_cases htail : i < remainder input
    · have hcand : ¬(remainder input ≤ i ∧ i < remainder input + 1) := by omega
      rw [if_neg hcand,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
      simp only [if_pos htail]
    · by_cases hsentinel : i = remainder input
      · subst i
        have hcand : remainder input ≤ remainder input ∧
            remainder input < remainder input + 1 := by omega
        rw [if_pos hcand]
        simp only [Nat.sub_self]
        rw [Challenge.EvmProof.Memory.getD0_eq_getElem!,
          getElem!_pos _ 0 (by omega)]
        simp only [if_neg (by omega)]
        rfl
      · have hafter : remainder input < i := by omega
        have hcand : ¬(remainder input ≤ i ∧ i < remainder input + 1) := by omega
        rw [if_neg hcand,
          Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
        have hzero : i < remainder input + 1 + (119 - input.size % 64) := by
          simp only [remainder]
          omega
        simp only [if_neg htail, if_neg hsentinel, if_pos hzero]
        apply Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
        have hadd := tailOffset_add_remainder input
        omega

theorem shortPaddedBlock_eq_canonical (input : ByteArray)
    (hshort : remainder input < 56) :
    shortPaddedBlock input = Ref.canonicalTail input := by
  apply ByteArray.ext_getElem
  · rw [shortPaddedBlock_size, canonicalTail_size_short input hshort]
  · intro i hleft hright
    have hi : i < 64 := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      canonicalTail_getD]
    unfold shortPaddedBlock
    rw [MachineState.writeBytes_getElem?_getD, Ref.lengthBytes_size]
    rw [Ref.zeroCount_eq]
    have hshortMod : input.size % 64 < 56 := by
      simpa [remainder] using hshort
    simp only [if_pos hshortMod]
    by_cases hfooter : 56 ≤ i
    · have hcand : 56 ≤ i ∧ i < 56 + 8 := by omega
      rw [if_pos hcand]
      have hnotTail : ¬ i < remainder input := by omega
      have hnotSent : ¬ i = remainder input := by omega
      have hnotZero : ¬ i < remainder input + 1 +
          (55 - input.size % 64) := by
        simp only [remainder] at hshort ⊢
        omega
      simp only [if_neg hnotTail, if_neg hnotSent, if_neg hnotZero]
      congr 3 <;> simp only [remainder] at * <;> omega
    · have hcand : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
      rw [if_neg hcand]
      unfold firstPaddedBlock
      rw [MachineState.writeBytes_getElem?_getD]
      have hone : (ByteArray.mk #[0x80]).size = 1 := rfl
      rw [hone]
      by_cases htail : i < remainder input
      · have hsentCond : ¬(remainder input ≤ i ∧
            i < remainder input + 1) := by omega
        rw [if_neg hsentCond,
          Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
        simp only [if_pos htail]
      · by_cases hsentinel : i = remainder input
        · subst i
          have hsentCond : remainder input ≤ remainder input ∧
              remainder input < remainder input + 1 := by omega
          rw [if_pos hsentCond]
          simp only [Nat.sub_self]
          rw [Challenge.EvmProof.Memory.getD0_eq_getElem!,
            getElem!_pos _ 0 (by omega)]
          simp only [if_neg (by omega)]
          rfl
        · have hafter : remainder input < i := by omega
          have hsentCond : ¬(remainder input ≤ i ∧
              i < remainder input + 1) := by omega
          rw [if_neg hsentCond,
            Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
          have hzero : i < remainder input + 1 +
              (55 - input.size % 64) := by
            simp only [remainder] at hshort ⊢
            omega
          simp only [if_neg htail, if_neg hsentinel, if_pos hzero]
          apply Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
          have hadd := tailOffset_add_remainder input
          omega

theorem lastPaddedBlock_eq_canonical_last (input : ByteArray)
    (hlong : ¬ remainder input < 56) :
    lastPaddedBlock input =
      MachineState.readPadded (Ref.canonicalTail input) 64 64 := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < 64 := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi,
      canonicalTail_getD]
    unfold lastPaddedBlock
    rw [MachineState.writeBytes_getElem?_getD, Ref.lengthBytes_size]
    rw [Ref.zeroCount_eq]
    have hlongMod : ¬ input.size % 64 < 56 := by
      simpa [remainder] using hlong
    simp only [if_neg hlongMod]
    have hr := Nat.mod_lt input.size (by omega : 0 < 64)
    have hend : remainder input + 1 + (119 - input.size % 64) = 120 := by
      simp only [remainder]
      omega
    by_cases hfooter : 56 ≤ i
    · have hcand : 56 ≤ i ∧ i < 56 + 8 := by omega
      rw [if_pos hcand]
      have hnotTail : ¬64 + i < remainder input := by
        simp only [remainder]
        omega
      have hnotSent : ¬64 + i = remainder input := by
        simp only [remainder]
        omega
      have hnotZero : ¬64 + i < remainder input + 1 +
          (119 - input.size % 64) := by
        rw [hend]
        omega
      simp only [if_neg hnotTail, if_neg hnotSent, if_neg hnotZero]
      have hidx : 64 + i - (remainder input + 1 +
          (119 - input.size % 64)) = i - 56 := by
        rw [hend]
        omega
      rw [hidx]
    · have hcand : ¬(56 ≤ i ∧ i < 56 + 8) := by omega
      rw [if_neg hcand]
      have hnotTail : ¬64 + i < remainder input := by
        simp only [remainder]
        omega
      have hnotSent : ¬64 + i = remainder input := by
        simp only [remainder]
        omega
      have hzero : 64 + i < remainder input + 1 +
          (119 - input.size % 64) := by
        rw [hend]
        omega
      simp only [if_neg hnotTail, if_neg hnotSent, if_pos hzero]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
        0 64 i hi]
      simp

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailMemoryBridge
