import Challenge.Modexp.Reference.Proofs.Bytecode.BigHelpers
import Mathlib.Data.List.GetD
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Certified multi-limb modular multiplication

This module composes the certified clear, copy, and masked-add helpers with
the emitted constant-shape double-and-add loops for `mulModBig`.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigMul

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Reference.Proofs.Bytecode

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def mulToClearPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 265 .JUMPDEST, pushAt 266 2 320,
   opAt 267 (.Dup ⟨5, by decide⟩), opAt 268 (.Dup ⟨4, by decide⟩),
   pushAt 269 2 19, opAt 270 .JUMP]

def mulToCopyPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 271 .JUMPDEST, pushAt 272 2 333,
   opAt 273 (.Dup ⟨5, by decide⟩), opAt 274 (.Dup ⟨2, by decide⟩),
   pushAt 275 2 4096, pushAt 276 2 58, opAt 277 .JUMP]

def mulSetupPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 278 .JUMPDEST, pushAt 279 0 0]

def mulOuterGuardPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 280 .JUMPDEST, opAt 281 (.Dup ⟨5, by decide⟩),
   opAt 282 (.Dup ⟨1, by decide⟩), opAt 283 .LT, opAt 284 .ISZERO,
   pushAt 285 2 426, opAt 286 .JUMPI]

def mulOuterLoadPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 287 (.Dup ⟨0, by decide⟩), pushAt 288 1 5, opAt 289 .SHL,
   opAt 290 (.Dup ⟨3, by decide⟩), opAt 291 .ADD, opAt 292 .MLOAD,
   pushAt 293 0 0]

def mulInnerGuardPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 294 .JUMPDEST, pushAt 295 2 256,
   opAt 296 (.Dup ⟨1, by decide⟩), opAt 297 .LT, opAt 298 .ISZERO,
   pushAt 299 2 413, opAt 300 .JUMPI]

def mulInnerToAddPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [pushAt 301 1 1, opAt 302 (.Dup ⟨2, by decide⟩),
   opAt 303 (.Dup ⟨2, by decide⟩), opAt 304 .SHR, opAt 305 .AND,
   pushAt 306 2 383, opAt 307 (.Dup ⟨9, by decide⟩),
   opAt 308 (.Dup ⟨9, by decide⟩), opAt 309 (.Dup ⟨3, by decide⟩),
   pushAt 310 2 4096, opAt 311 (.Dup ⟨11, by decide⟩),
   pushAt 312 2 104, opAt 313 .JUMP]

def mulAddToDoublePath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 314 .JUMPDEST, pushAt 315 2 401,
   opAt 316 (.Dup ⟨9, by decide⟩), opAt 317 (.Dup ⟨9, by decide⟩),
   pushAt 318 1 1, pushAt 319 2 4096, pushAt 320 2 4096,
   pushAt 321 2 104, opAt 322 .JUMP]

def mulDoubleToNextPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 323 .JUMPDEST, opAt 324 .POP, pushAt 325 1 1,
   opAt 326 (.Dup ⟨1, by decide⟩), opAt 327 .ADD,
   opAt 328 (.Swap ⟨0, by decide⟩), opAt 329 .POP,
   pushAt 330 2 352, opAt 331 .JUMP]

def mulInnerToOuterPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 332 .JUMPDEST, opAt 333 .POP, opAt 334 .POP,
   pushAt 335 1 1, opAt 336 (.Dup ⟨1, by decide⟩), opAt 337 .ADD,
   opAt 338 (.Swap ⟨0, by decide⟩), opAt 339 .POP,
   pushAt 340 2 335, opAt 341 .JUMP]

def mulOuterExitPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka) :=
  [opAt 342 .JUMPDEST, opAt 343 .POP, opAt 344 .POP, opAt 345 .POP,
   opAt 346 .POP, opAt 347 .POP, opAt 348 .POP, opAt 349 .JUMP]

def mulEntry (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 310
           stack := [a, b, out, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

def mulAfterClear (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 320
           stack := [a, b, out, modulus, UInt256.ofNat count,
             returnDest] ++ rest
           memory := BigHelpers.clearMemory s.memory out count
           activeWords := BigHelpers.clearWords s.activeWords out count }

def mulAfterCopy (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let cleared := mulAfterClear s a b out modulus count returnDest rest
  { cleared with
    pc := UInt256.ofNat 333
    memory := BigHelpers.copyMemory cleared.memory (UInt256.ofNat 4096) a count
    activeWords := BigHelpers.copyWords cleared.activeWords
      (UInt256.ofNat 4096) a count }

def mulOuterLoop (s : State) (a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let copied := mulAfterCopy s a b out modulus count returnDest rest
  { copied with
    pc := UInt256.ofNat 335
    stack := [UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
      returnDest] ++ rest }

def mulOuterBody (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with
    pc := UInt256.ofNat 344
    stack := [UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
      returnDest] ++ rest }

/-- Inner-loop state with the multiplier word fixed after its single `MLOAD`.
This form is used to iterate all 256 bits without re-reading memory. -/
def mulInnerState (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with
    pc := UInt256.ofNat 352
    stack := [UInt256.ofNat j, word, UInt256.ofNat i, a, b, out, modulus,
      UInt256.ofNat count, returnDest] ++ rest }

def mulWordBit (word : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat j)) (UInt256.ofNat 1)

def mulWordRest (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [mulWordBit word j, UInt256.ofNat j, word, UInt256.ofNat i, a, b, out,
    modulus, UInt256.ofNat count, returnDest] ++ rest

def mulWordAfterAdd (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let inner := mulInnerState current word a b out modulus count i j
    returnDest rest
  BigHelpers.addReturned inner out (UInt256.ofNat 4096) (mulWordBit word j)
    modulus count (UInt256.ofNat 383)
    (mulWordRest word a b out modulus count i j returnDest rest)

def mulWordAfterDouble (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let afterAdd := mulWordAfterAdd current word a b out modulus count i j
    returnDest rest
  BigHelpers.addReturned afterAdd (UInt256.ofNat 4096) (UInt256.ofNat 4096)
    (UInt256.ofNat 1) modulus count (UInt256.ofNat 401)
    (mulWordRest word a b out modulus count i j returnDest rest)

def mulWordInnerNext (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let doubled := mulWordAfterDouble current word a b out modulus count i j
    returnDest rest
  mulInnerState doubled word a b out modulus count i (j + 1) returnDest rest

def mulWordBits (word : UInt256) (length : Nat) : List Nat :=
  (List.range length).map fun j => (mulWordBit word j).toNat

def mulWordProgress (current : State) (word a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : Nat → State
  | 0 => current
  | j + 1 => mulWordAfterDouble
      (mulWordProgress current word a b out modulus count i returnDest rest j)
      word a b out modulus count i j returnDest rest

@[simp] theorem mulWordProgress_executionEnv (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) :
    (mulWordProgress current word a b out modulus count i returnDest rest j).executionEnv =
      current.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [mulWordProgress, mulWordAfterDouble, mulWordAfterAdd,
        mulInnerState, BigHelpers.addReturned, ih]

@[simp] theorem mulWordProgress_halt (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) :
    (mulWordProgress current word a b out modulus count i returnDest rest j).halt =
      current.halt := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [mulWordProgress, mulWordAfterDouble, mulWordAfterAdd,
        mulInnerState, BigHelpers.addReturned, ih]

def mulInnerLoop (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  let bAt := b + off
  let word := MachineState.readWord current.memory bAt.toNat
  { current with
    pc := UInt256.ofNat 352
    stack := [UInt256.ofNat j, word, UInt256.ofNat i, a, b, out, modulus,
      UInt256.ofNat count, returnDest] ++ rest
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      current.activeWords.toNat bAt.toNat 32) }

def mulLoadedState (current : State) (b : UInt256) (i : Nat) : State :=
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  let bAt := b + off
  { current with activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      current.activeWords.toNat bAt.toNat 32) }

def mulLoadedWord (current : State) (b : UInt256) (i : Nat) : UInt256 :=
  MachineState.readWord current.memory
    (b + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat

theorem mulInnerLoop_eq_state (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) :
    mulInnerLoop current a b out modulus count i j returnDest rest =
      mulInnerState (mulLoadedState current b i) (mulLoadedWord current b i)
        a b out modulus count i j returnDest rest := by
  rfl

def mulBit (current : State) (b : UInt256) (i j : Nat) : UInt256 :=
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  let word := MachineState.readWord current.memory (b + off).toNat
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat j)) (UInt256.ofNat 1)

theorem mulBit_toNat_le_one (current : State) (b : UInt256) (i j : Nat) :
    (mulBit current b i j).toNat ≤ 1 := by
  rw [mulBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]
  exact Nat.and_le_right

theorem mulWordBit_toNat_le_one (word : UInt256) (j : Nat) :
    (mulWordBit word j).toNat ≤ 1 := by
  rw [mulWordBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]
  exact Nat.and_le_right

theorem mulWordBit_toNat (word : UInt256) {j : Nat} (hj : j < 256) :
    (mulWordBit word j).toNat = (word.toNat >>> j) &&& 1 := by
  rw [mulWordBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat word hj,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]

theorem mulWordBits_eq_digitsAppend (word : UInt256) :
    mulWordBits word 256 = Nat.digitsAppend 2 256 word.toNat := by
  apply List.ext_get
  · simp [mulWordBits,
      Nat.length_digitsAppend (n := word.toNat) (by norm_num) 256 word.val.isLt]
  · intro j hleft hright
    have hj : j < 256 := by simpa [mulWordBits] using hleft
    have hleftValue :
        (mulWordBits word 256).get ⟨j, hleft⟩ =
          (mulWordBit word j).toNat := by
      simp [mulWordBits]
    rw [hleftValue]
    rw [mulWordBit_toNat word hj, Nat.and_one_is_mod]
    have hrightValue :
        (Nat.digitsAppend 2 256 word.toNat).get ⟨j, hright⟩ =
          (Nat.digitsAppend 2 256 word.toNat).getD j 0 :=
      (List.getD_eq_getElem
        (Nat.digitsAppend 2 256 word.toNat) 0 hright).symm
    rw [hrightValue]
    have hpadded :
        (Nat.digitsAppend 2 256 word.toNat).getD j 0 =
          (Nat.digits 2 word.toNat).getD j 0 := by
      rw [Nat.digitsAppend]
      by_cases hdigit : j < (Nat.digits 2 word.toNat).length
      · rw [List.getD_append _ _ _ _ hdigit]
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hdigit),
          List.getD_eq_default _ _ (Nat.le_of_not_gt hdigit)]
        simp [List.getD_eq_getElem?_getD]
    rw [hpadded, Nat.getD_digits word.toNat j (by omega),
      Nat.shiftRight_eq_div_pow]

theorem value_mulWordBits (word : UInt256) :
    Nat.ofDigits 2 (mulWordBits word 256) = word.toNat := by
  rw [mulWordBits_eq_digitsAppend, Nat.digitsAppend,
    Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

def mulBitRest (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [mulBit current b i j, UInt256.ofNat j,
    MachineState.readWord current.memory
      (b + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat,
    UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
    returnDest] ++ rest

def mulAfterBitAdd (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let inner := mulInnerLoop current a b out modulus count i j returnDest rest
  let bit := mulBit current b i j
  BigHelpers.addReturned inner out (UInt256.ofNat 4096) bit modulus count
    (UInt256.ofNat 383)
    (mulBitRest current a b out modulus count i j returnDest rest)

def mulAfterBitDouble (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let afterAdd := mulAfterBitAdd current a b out modulus count i j
    returnDest rest
  BigHelpers.addReturned afterAdd (UInt256.ofNat 4096) (UInt256.ofNat 4096)
    (UInt256.ofNat 1) modulus count (UInt256.ofNat 401)
    (mulBitRest current a b out modulus count i j returnDest rest)

def mulInnerNext (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let doubled := mulAfterBitDouble current a b out modulus count i j
    returnDest rest
  let word := MachineState.readWord current.memory
    (b + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat
  { doubled with
    pc := UInt256.ofNat 352
    stack := [UInt256.ofNat (j + 1), word, UInt256.ofNat i, a, b, out,
      modulus, UInt256.ofNat count, returnDest] ++ rest }

def mulOuterNext (inner : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { inner with
    pc := UInt256.ofNat 335
    stack := [UInt256.ofNat (i + 1), a, b, out, modulus,
      UInt256.ofNat count, returnDest] ++ rest }

def mulOuterState (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with
    pc := UInt256.ofNat 335
    stack := [UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
      returnDest] ++ rest }

def mulReturned (current : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := returnDest, stack := rest }

theorem mulOuterNext_innerState (current : State) (word a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) :
    mulOuterNext
        (mulInnerState current word a b out modulus count i 256 returnDest rest)
        a b out modulus count i returnDest rest =
      mulOuterState current a b out modulus count (i + 1) returnDest rest := by
  rfl

def mulOuterProgress (current : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) : Nat → State
  | 0 => current
  | i + 1 =>
      let before := mulOuterProgress current a b out modulus count
        returnDest rest i
      let loaded := mulLoadedState before b i
      let word := mulLoadedWord before b i
      mulWordProgress loaded word a b out modulus count i returnDest rest 256

def mulOuterBits (memory : ByteArray) (bPtr steps : Nat) : List Nat :=
  (List.range steps).flatMap fun i =>
    mulWordBits (MachineState.readWord memory (bPtr + 32 * i)) 256

theorem mulOuterBits_succ (memory : ByteArray) (bPtr i : Nat) :
    mulOuterBits memory bPtr (i + 1) =
      mulOuterBits memory bPtr i ++
        mulWordBits (MachineState.readWord memory (bPtr + 32 * i)) 256 := by
  simp [mulOuterBits, List.range_succ]

@[simp] theorem length_mulOuterBits (memory : ByteArray) (bPtr steps : Nat) :
    (mulOuterBits memory bPtr steps).length = 256 * steps := by
  simp [mulOuterBits, mulWordBits]
  omega

theorem value_mulOuterBits (memory : ByteArray) (bPtr count : Nat) :
    Nat.ofDigits 2 (mulOuterBits memory bPtr count) =
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory bPtr count) := by
  induction count with
  | zero => simp [mulOuterBits, Limbs.memoryLimbs]
  | succ count ih =>
      rw [mulOuterBits_succ, Nat.ofDigits_append, ih, value_mulWordBits]
      simp [Limbs.memoryLimbs, List.range_succ, Nat.ofDigits_append,
        Limbs.radix, Nat.pow_mul]

theorem readWord_eq_of_represents (left right : ByteArray)
    (ptr count value i : Nat) (hi : i < count)
    (hleft : Limbs.Represents left ptr count value)
    (hright : Limbs.Represents right ptr count value) :
    MachineState.readWord left (ptr + 32 * i) =
      MachineState.readWord right (ptr + 32 * i) := by
  have hlists : Limbs.memoryLimbs left ptr count =
      Limbs.memoryLimbs right ptr count := hleft.2.trans hright.2.symm
  have hget := congrArg (fun digits => digits[i]?) hlists
  have htoNat :
      (MachineState.readWord left (ptr + 32 * i)).toNat =
        (MachineState.readWord right (ptr + 32 * i)).toNat := by
    simpa [Limbs.memoryLimbs, hi] using hget
  calc
    MachineState.readWord left (ptr + 32 * i) =
        UInt256.ofNat (MachineState.readWord left (ptr + 32 * i)).toNat :=
      Challenge.EvmProof.Word.word_eq_ofNat_toNat _
    _ = UInt256.ofNat (MachineState.readWord right (ptr + 32 * i)).toNat := by
      rw [htoNat]
    _ = MachineState.readWord right (ptr + 32 * i) :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

@[simp] theorem mulOuterProgress_executionEnv (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (mulOuterProgress current a b out modulus count returnDest rest i).executionEnv =
      current.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [mulOuterProgress, mulLoadedState, ih]

@[simp] theorem mulOuterProgress_halt (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (mulOuterProgress current a b out modulus count returnDest rest i).halt =
      current.halt := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [mulOuterProgress, mulLoadedState, ih]

@[simp] private theorem mulPCs (i : Nat) (hi : 265 ≤ i) (hii : i ≤ 279) :
    Artifact.referenceArtifact.instructionPC i =
      [310,311,314,315,316,319,320,321,324,325,326,329,332,333,334][i - 265]! := by
  interval_cases i <;> decide

@[simp] private theorem listGetZero {α : Type} (head default : α)
    (tail : List α) :
    (head :: tail)[0]?.getD default = head := by
  rfl

@[simp] private theorem listGetElemZero {α : Type} (head : α)
    (tail : List α) :
    (head :: tail)[0]? = some head := by
  rfl

@[simp] private theorem mulLoopPCs (i : Nat) (hi : 280 ≤ i) (hii : i ≤ 300) :
    Artifact.referenceArtifact.instructionPC i =
      [335,336,337,338,339,340,343,344,345,347,348,349,350,351,352,
       353,356,357,358,359,362][i - 280]! := by
  interval_cases i <;> decide

@[simp] private theorem mulInnerPCs (i : Nat) (hi : 301 ≤ i) (hii : i ≤ 322) :
    Artifact.referenceArtifact.instructionPC i =
      [363,365,366,367,368,369,372,373,374,375,378,379,382,383,384,
       387,388,389,391,394,397,400][i - 301]! := by
  interval_cases i <;> decide

@[simp] private theorem mulNextPCs (i : Nat) (hi : 323 ≤ i) (hii : i ≤ 331) :
    Artifact.referenceArtifact.instructionPC i =
      [401,402,403,405,406,407,408,409,412][i - 323]! := by
  interval_cases i <;> decide

@[simp] private theorem mulInnerExitPCs (i : Nat) (hi : 332 ≤ i)
    (hii : i ≤ 341) :
    Artifact.referenceArtifact.instructionPC i =
      [413,414,415,416,418,419,420,421,422,425][i - 332]! := by
  interval_cases i <;> decide

@[simp] private theorem mulReturnPCs (i : Nat) (hi : 342 ≤ i)
    (hii : i ≤ 349) :
    Artifact.referenceArtifact.instructionPC i =
      [426,427,428,429,430,431,432,433][i - 342]! := by
  interval_cases i <;> decide

private theorem jump335 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 335 = true :=
  Artifact.isValidJumpDest_index 280 (by rfl)

private theorem jump352 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 352 = true :=
  Artifact.isValidJumpDest_index 294 (by rfl)

private theorem jump383 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 383 = true :=
  Artifact.isValidJumpDest_index 314 (by rfl)

private theorem jump401 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 401 = true :=
  Artifact.isValidJumpDest_index 323 (by rfl)

private theorem jump104 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

private theorem jump19 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump58 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 58 = true :=
  Artifact.isValidJumpDest_index 46 (by rfl)

private theorem jump320 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 320 = true :=
  Artifact.isValidJumpDest_index 271 (by rfl)

private theorem jump333 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 333 = true :=
  Artifact.isValidJumpDest_index 278 (by rfl)

private theorem jump413 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 413 = true :=
  Artifact.isValidJumpDest_index 332 (by rfl)

private theorem jump426 :
    Decode.isValidJumpDest Challenge.Modexp.referenceBytecode 426 = true :=
  Artifact.isValidJumpDest_index 342 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_mulToClear (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1012) (hcode : s.executionEnv.code =
      Challenge.Modexp.referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulToClearPath
      (mulEntry s a b out modulus count returnDest rest) =
    some (BigHelpers.clearEntry s out count (UInt256.ofNat 320)
      ([a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest)) := by
  have hc : ∀ n ≤ 12, rest.length + n < 1024 := by omega
  have h19 : (19 : UInt256) = UInt256.ofNat 19 := by decide
  have h320 : (320 : UInt256) = UInt256.ofNat 320 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (19 : UInt256).toNat = true := by
    rw [show (19 : UInt256).toNat = 19 by decide]
    exact jump19
  simp (disch := omega) [mulToClearPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulEntry, BigHelpers.clearEntry, mulPCs, hcode, hrun, hvalid, jump19,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc,
    hc, h19, h320]

set_option linter.unusedSimpArgs false in
theorem run_mulToCopy (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1012) (hcode : s.executionEnv.code =
      Challenge.Modexp.referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulToCopyPath
      (mulAfterClear s a b out modulus count returnDest rest) =
    some (BigHelpers.copyEntry (mulAfterClear s a b out modulus count
      returnDest rest) (UInt256.ofNat 4096) a count (UInt256.ofNat 333)
      ([a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest)) := by
  have hc : ∀ n ≤ 12, rest.length + n < 1024 := by omega
  have h58 : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have h333 : (333 : UInt256) = UInt256.ofNat 333 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (58 : UInt256).toNat = true := by
    rw [show (58 : UInt256).toNat = 58 by decide]
    exact jump58
  simp (disch := omega) [mulToCopyPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulAfterClear, BigHelpers.copyEntry, mulPCs, hcode, hrun, hvalid, jump58,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc,
    hc, h58, h333, h4096]

set_option linter.unusedSimpArgs false in
theorem run_mulSetup (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1012) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulSetupPath
      (mulAfterCopy s a b out modulus count returnDest rest) =
    some (mulOuterLoop s a b out modulus count 0 returnDest rest) := by
  have hc : ∀ n ≤ 12, rest.length + n < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (disch := omega) [mulSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulAfterCopy, mulAfterClear, mulOuterLoop, mulPCs, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc, hc, hzero]

set_option linter.unusedSimpArgs false in
theorem run_mulOuterGuard (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1014) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulOuterGuardPath
      { current with
        pc := UInt256.ofNat 335
        stack := [UInt256.ofNat i, a, b, out, modulus,
          UInt256.ofNat count, returnDest] ++ rest } =
    some (mulOuterBody current a b out modulus count i returnDest rest) := by
  have hc : ∀ n ≤ 10, rest.length + n < 1024 := by omega
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (disch := omega) [mulOuterGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulOuterBody, mulLoopPCs, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero, Nat.add_assoc, hc, hi]

set_option linter.unusedSimpArgs false in
theorem run_mulOuterFinishGuard (current : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1014) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulOuterGuardPath
      (mulOuterState current a b out modulus count count returnDest rest) =
    some { mulOuterState current a b out modulus count count returnDest rest with
      pc := UInt256.ofNat 426 } := by
  have hc : ∀ n ≤ 10, rest.length + n < 1024 := by omega
  have h426 : (426 : UInt256) = UInt256.ofNat 426 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (426 : UInt256).toNat = true := by
    rw [show (426 : UInt256).toNat = 426 by decide]
    exact jump426
  simp (disch := omega) [mulOuterGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulOuterState, mulLoopPCs, hcode, hrun, UInt256.lt, UInt256.isTrue,
    hzeroFalse, hvalid, jump426,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h426]

set_option linter.unusedSimpArgs false in
theorem run_mulOuterExit (current : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1014)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulOuterExitPath
      { mulOuterState current a b out modulus count count returnDest rest with
        pc := UInt256.ofNat 426 } =
    some (mulReturned current returnDest rest) := by
  have hc : ∀ n ≤ 10, rest.length + n < 1024 := by omega
  simp (disch := omega) [mulOuterExitPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulOuterState, mulReturned, mulReturnPCs, hcode, hrun, hvalid,
    Challenge.EvmProof.Word.succ_ofNat_mod, List.exchange, Nat.add_assoc, hc]

set_option linter.unusedSimpArgs false in
theorem run_mulOuterLoad (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1014) (_hi : i < 2 ^ 256)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulOuterLoadPath
      (mulOuterBody current a b out modulus count i returnDest rest) =
    some (mulInnerLoop current a b out modulus count i 0 returnDest rest) := by
  have hc : ∀ n ≤ 10, rest.length + n < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 300000 }) (disch := omega)
    [mulOuterLoadPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulOuterBody, mulInnerLoop, mulLoopPCs, hrun, hfive, hzero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc]
  exact hzero

set_option linter.unusedSimpArgs false in
theorem run_mulInnerGuard (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hj : j < 256)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerGuardPath
      (mulInnerLoop current a b out modulus count i j returnDest rest) =
    some { mulInnerLoop current a b out modulus count i j returnDest rest with
      pc := UInt256.ofNat 363 } := by
  have hc : ∀ n ≤ 11, rest.length + n < 1024 := by omega
  have h256Nat : (256 : UInt256).toNat = 256 := by decide
  have hlt : j % 2 ^ 256 < 256 % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)]
    exact hj
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (disch := omega) [mulInnerGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerLoop, mulLoopPCs, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero, Nat.add_assoc, hc, h256Nat, hj]

set_option linter.unusedSimpArgs false in
theorem run_mulWordInnerGuard (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hj : j < 256)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerGuardPath
      (mulInnerState current word a b out modulus count i j returnDest rest) =
    some { mulInnerState current word a b out modulus count i j returnDest rest
      with pc := UInt256.ofNat 363 } := by
  have hc : ∀ n ≤ 11, rest.length + n < 1024 := by omega
  have h256Nat : (256 : UInt256).toNat = 256 := by decide
  have hlt : j % 2 ^ 256 < 256 % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)]
    exact hj
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (disch := omega) [mulInnerGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerState, mulLoopPCs, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero, Nat.add_assoc, hc, h256Nat, hj]

set_option linter.unusedSimpArgs false in
theorem run_mulInnerFinishGuard (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hcode : current.executionEnv.code =
      Challenge.Modexp.referenceBytecode) (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerGuardPath
      (mulInnerLoop current a b out modulus count i 256 returnDest rest) =
    some { mulInnerLoop current a b out modulus count i 256 returnDest rest with
      pc := UInt256.ofNat 413 } := by
  have hc : ∀ n ≤ 11, rest.length + n < 1024 := by omega
  have h256Nat : (256 : UInt256).toNat = 256 := by decide
  have h413 : (413 : UInt256) = UInt256.ofNat 413 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (413 : UInt256).toNat = true := by
    rw [show (413 : UInt256).toNat = 413 by decide]
    exact jump413
  simp (disch := omega) [mulInnerGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerLoop, mulLoopPCs, hcode, hrun, UInt256.lt, UInt256.isTrue,
    hzeroFalse, hvalid, jump413,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h256Nat, h413]

set_option linter.unusedSimpArgs false in
theorem run_mulWordInnerFinishGuard (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hcode : current.executionEnv.code =
      Challenge.Modexp.referenceBytecode) (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerGuardPath
      (mulInnerState current word a b out modulus count i 256 returnDest rest) =
    some { mulInnerState current word a b out modulus count i 256
      returnDest rest with pc := UInt256.ofNat 413 } := by
  have hc : ∀ n ≤ 11, rest.length + n < 1024 := by omega
  have h256Nat : (256 : UInt256).toNat = 256 := by decide
  have h413 : (413 : UInt256) = UInt256.ofNat 413 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (413 : UInt256).toNat = true := by
    rw [show (413 : UInt256).toNat = 413 by decide]
    exact jump413
  simp (disch := omega) [mulInnerGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerState, mulLoopPCs, hcode, hrun, UInt256.lt, UInt256.isTrue,
    hzeroFalse, hvalid, jump413,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h256Nat, h413]

set_option linter.unusedSimpArgs false in
theorem run_mulInnerToOuter (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hi : i + 1 < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    let inner := mulInnerLoop current a b out modulus count i 256 returnDest rest
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerToOuterPath
      { inner with pc := UInt256.ofNat 413 } =
    some (mulOuterNext inner a b out modulus count i returnDest rest) := by
  dsimp only
  have hc : ∀ n ≤ 11, rest.length + n < 1024 := by omega
  have h335 : (335 : UInt256) = UInt256.ofNat 335 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (335 : UInt256).toNat = true := by
    rw [show (335 : UInt256).toNat = 335 by decide]
    exact jump335
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat (a := i) (b := 1) hi
  simp (disch := omega) [mulInnerToOuterPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerLoop, mulOuterNext, mulInnerExitPCs, hcode, hrun, hvalid,
    jump335, hinc, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    List.exchange, Nat.add_assoc, hc, h335, hone]

set_option linter.unusedSimpArgs false in
theorem run_mulWordInnerToOuter (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hi : i + 1 < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    let inner := mulInnerState current word a b out modulus count i 256
      returnDest rest
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerToOuterPath
      { inner with pc := UInt256.ofNat 413 } =
    some (mulOuterNext inner a b out modulus count i returnDest rest) := by
  dsimp only
  have hc : ∀ n ≤ 11, rest.length + n < 1024 := by omega
  have h335 : (335 : UInt256) = UInt256.ofNat 335 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (335 : UInt256).toNat = true := by
    rw [show (335 : UInt256).toNat = 335 by decide]
    exact jump335
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat (a := i) (b := 1) hi
  simp (disch := omega) [mulInnerToOuterPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerState, mulOuterNext, mulInnerExitPCs, hcode, hrun, hvalid,
    jump335, hinc, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    List.exchange, Nat.add_assoc, hc, h335, hone]

set_option linter.unusedSimpArgs false in
theorem run_mulInnerToAdd (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1007) (_hj : j < 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerToAddPath
      { mulInnerLoop current a b out modulus count i j returnDest rest with
        pc := UInt256.ofNat 363 } =
    some (BigHelpers.addEntry
      (mulInnerLoop current a b out modulus count i j returnDest rest)
      out (UInt256.ofNat 4096) (mulBit current b i j) modulus count
      (UInt256.ofNat 383)
      (mulBitRest current a b out modulus count i j returnDest rest)) := by
  have hc : ∀ n ≤ 17, rest.length + n < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h383 : (383 : UInt256) = UInt256.ofNat 383 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (104 : UInt256).toNat = true := by
    rw [show (104 : UInt256).toNat = 104 by decide]
    exact jump104
  simp (config := { maxSteps := 500000 }) (disch := omega)
    [mulInnerToAddPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulInnerLoop, mulBit, mulBitRest, BigHelpers.addEntry, mulInnerPCs,
      hcode, hrun, hvalid, jump104,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc, hone, h104, h383, h4096]

set_option linter.unusedSimpArgs false in
theorem run_mulWordInnerToAdd (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1007) (_hj : j < 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerToAddPath
      { mulInnerState current word a b out modulus count i j returnDest rest with
        pc := UInt256.ofNat 363 } =
    some (BigHelpers.addEntry
      (mulInnerState current word a b out modulus count i j returnDest rest)
      out (UInt256.ofNat 4096) (mulWordBit word j) modulus count
      (UInt256.ofNat 383)
      (mulWordRest word a b out modulus count i j returnDest rest)) := by
  have hc : ∀ n ≤ 17, rest.length + n < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h383 : (383 : UInt256) = UInt256.ofNat 383 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (104 : UInt256).toNat = true := by
    rw [show (104 : UInt256).toNat = 104 by decide]
    exact jump104
  simp (config := { maxSteps := 500000 }) (disch := omega)
    [mulInnerToAddPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulInnerState, mulWordBit, mulWordRest, BigHelpers.addEntry,
      mulInnerPCs, hcode, hrun, hvalid, jump104,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc, hone, h104, h383, h4096]

set_option linter.unusedSimpArgs false in
theorem run_mulAddToDouble (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1007)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    let inner := mulInnerLoop current a b out modulus count i j returnDest rest
    let bit := mulBit current b i j
    let saved := mulBitRest current a b out modulus count i j returnDest rest
    let afterAdd := BigHelpers.addReturned inner out (UInt256.ofNat 4096) bit
      modulus count (UInt256.ofNat 383) saved
    Challenge.EvmProof.Stepper.runLocatedBlock mulAddToDoublePath afterAdd =
      some (BigHelpers.addEntry afterAdd (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 401) saved) := by
  dsimp only
  have hc : ∀ n ≤ 17, rest.length + n < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h401 : (401 : UInt256) = UInt256.ofNat 401 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (104 : UInt256).toNat = true := by
    rw [show (104 : UInt256).toNat = 104 by decide]
    exact jump104
  simp (config := { maxSteps := 500000 }) (disch := omega)
    [mulAddToDoublePath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulInnerLoop, BigHelpers.addReturned, BigHelpers.addEntry, mulInnerPCs,
      hcode, hrun, hvalid, jump104,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, mulBitRest, Nat.add_assoc, hc, hone, h104, h401, h4096]

set_option linter.unusedSimpArgs false in
theorem run_mulWordAddToDouble (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1007)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    let _inner := mulInnerState current word a b out modulus count i j
      returnDest rest
    let saved := mulWordRest word a b out modulus count i j returnDest rest
    let afterAdd := mulWordAfterAdd current word a b out modulus count i j
      returnDest rest
    Challenge.EvmProof.Stepper.runLocatedBlock mulAddToDoublePath afterAdd =
      some (BigHelpers.addEntry afterAdd (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 401) saved) := by
  dsimp only
  have hc : ∀ n ≤ 17, rest.length + n < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h401 : (401 : UInt256) = UInt256.ofNat 401 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (104 : UInt256).toNat = true := by
    rw [show (104 : UInt256).toNat = 104 by decide]
    exact jump104
  simp (config := { maxSteps := 500000 }) (disch := omega)
    [mulAddToDoublePath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulWordAfterAdd, mulInnerState, BigHelpers.addReturned, BigHelpers.addEntry,
      mulInnerPCs, hcode, hrun, hvalid, jump104,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, mulWordRest, Nat.add_assoc, hc, hone, h104, h401, h4096]

set_option linter.unusedSimpArgs false in
theorem run_mulDoubleToNext (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1007) (hj : j + 1 < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulDoubleToNextPath
      (mulAfterBitDouble current a b out modulus count i j returnDest rest) =
    some (mulInnerNext current a b out modulus count i j returnDest rest) := by
  have hc : ∀ n ≤ 17, rest.length + n < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h352 : (352 : UInt256) = UInt256.ofNat 352 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (352 : UInt256).toNat = true := by
    rw [show (352 : UInt256).toNat = 352 by decide]
    exact jump352
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) hj
  simp (config := { maxSteps := 400000 }) (disch := omega)
    [mulDoubleToNextPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulAfterBitDouble, mulAfterBitAdd, mulInnerNext, mulInnerLoop, mulBitRest,
      BigHelpers.addReturned, mulNextPCs, hcode, hrun, hvalid, jump352, hinc,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc, hone, h352]

set_option linter.unusedSimpArgs false in
theorem run_mulWordDoubleToNext (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1007) (hj : j + 1 < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulDoubleToNextPath
      (mulWordAfterDouble current word a b out modulus count i j
        returnDest rest) =
    some (mulWordInnerNext current word a b out modulus count i j
      returnDest rest) := by
  have hc : ∀ n ≤ 17, rest.length + n < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h352 : (352 : UInt256) = UInt256.ofNat 352 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      (352 : UInt256).toNat = true := by
    rw [show (352 : UInt256).toNat = 352 by decide]
    exact jump352
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) hj
  simp (config := { maxSteps := 400000 }) (disch := omega)
    [mulDoubleToNextPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulWordAfterDouble, mulWordAfterAdd, mulWordInnerNext, mulWordRest,
      mulInnerState, BigHelpers.addReturned, mulNextPCs, hcode, hrun,
      hvalid, jump352, hinc,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc, hone, h352]

def gasSteps_mulBitIteration (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulInnerLoop current a b out modulus count i j returnDest rest)
      (mulInnerNext current a b out modulus count i j returnDest rest) := by
  let inner := mulInnerLoop current a b out modulus count i j returnDest rest
  let bit := mulBit current b i j
  let saved := mulBitRest current a b out modulus count i j returnDest rest
  let afterAdd := mulAfterBitAdd current a b out modulus count i j
    returnDest rest
  let afterDouble := mulAfterBitDouble current a b out modulus count i j
    returnDest rest
  have hcapAdd : rest.length < 1007 := by omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulInnerGuardPath
      (by simpa [inner, mulInnerLoop,
        Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (run_mulInnerGuard current a b out modulus count i j returnDest rest
        (by omega) hj hrun)
      (by simpa [inner, mulInnerLoop] using hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hnp)
  have htoAdd := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulInnerToAddPath
      (by simpa [inner, mulInnerLoop,
        Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (run_mulInnerToAdd current a b out modulus count i j returnDest rest
        (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerLoop] using hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hnp)
  have hadd := BigHelpers.gasSteps_addMaskedMod inner out (UInt256.ofNat 4096)
    bit modulus count (UInt256.ofNat 383) saved
    (by simp [saved, mulBitRest]; omega)
    hcount (by simpa [inner, mulInnerLoop] using hcode)
    (by simpa [inner, mulInnerLoop, State.fork] using hfork)
    (by simpa [inner, mulInnerLoop] using hrun)
    (by simpa [inner, mulInnerLoop, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have hadd' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry inner out (UInt256.ofNat 4096) bit modulus count
        (UInt256.ofNat 383) saved) afterAdd := by
    exact Challenge.EvmProof.GasSteps.cast hadd rfl (by
      simp [afterAdd, mulAfterBitAdd, inner, bit, saved])
  have hrunToDouble := run_mulAddToDouble current a b out modulus count i j
    returnDest rest hcapAdd hcode hrun
  have htoDouble := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulAddToDoublePath (s := afterAdd)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, Artifact.referenceArtifact] using hcode)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterAdd, mulAfterBitAdd, inner, bit, saved] using
        hrunToDouble)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned] using hrun)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, State.fork] using hnp)
  have hdouble := BigHelpers.gasSteps_addMaskedMod afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved
    (by simp [saved, mulBitRest]; omega) hcount
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hdouble' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry afterAdd (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 401) saved) afterDouble := by
    exact Challenge.EvmProof.GasSteps.cast hdouble rfl (by
      simp [afterDouble, mulAfterBitDouble, afterAdd, saved])
  have hrunNext := run_mulDoubleToNext current a b out modulus count i j
    returnDest rest hcapAdd (by omega) hcode hrun
  have hnext := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulDoubleToNextPath (s := afterDouble)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned,
        Artifact.referenceArtifact] using hcode)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterDouble] using hrunNext)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned] using hrun)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned, State.fork] using hnp)
  exact hguard.trans <| htoAdd.trans <| hadd'.trans <|
    htoDouble.trans <| hdouble'.trans hnext

def gasSteps_mulWordBitIteration (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulInnerState current word a b out modulus count i j returnDest rest)
      (mulWordInnerNext current word a b out modulus count i j
        returnDest rest) := by
  let inner := mulInnerState current word a b out modulus count i j
    returnDest rest
  let bit := mulWordBit word j
  let saved := mulWordRest word a b out modulus count i j returnDest rest
  let afterAdd := mulWordAfterAdd current word a b out modulus count i j
    returnDest rest
  let afterDouble := mulWordAfterDouble current word a b out modulus count i j
    returnDest rest
  have hcapAdd : rest.length < 1007 := by omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulInnerGuardPath
      (by simpa [inner, mulInnerState,
        Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (run_mulWordInnerGuard current word a b out modulus count i j returnDest
        rest (by omega) hj hrun)
      (by simpa [inner, mulInnerState] using hrun)
      (by simpa [inner, mulInnerState, State.fork] using hnp)
  have htoAdd := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulInnerToAddPath
      (by simpa [inner, mulInnerState,
        Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (run_mulWordInnerToAdd current word a b out modulus count i j returnDest
        rest (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerState] using hrun)
      (by simpa [inner, mulInnerState, State.fork] using hnp)
  have hadd := BigHelpers.gasSteps_addMaskedMod inner out (UInt256.ofNat 4096)
    bit modulus count (UInt256.ofNat 383) saved
    (by simp [saved, mulWordRest]; omega)
    hcount (by simpa [inner, mulInnerState] using hcode)
    (by simpa [inner, mulInnerState, State.fork] using hfork)
    (by simpa [inner, mulInnerState] using hrun)
    (by simpa [inner, mulInnerState, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have hadd' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry inner out (UInt256.ofNat 4096) bit modulus count
        (UInt256.ofNat 383) saved) afterAdd := by
    exact Challenge.EvmProof.GasSteps.cast hadd rfl (by
      simp [afterAdd, mulWordAfterAdd, inner, bit, saved])
  have hrunToDouble := run_mulWordAddToDouble current word a b out modulus
    count i j returnDest rest hcapAdd hcode hrun
  have htoDouble := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulAddToDoublePath (s := afterAdd)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, Artifact.referenceArtifact] using hcode)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterAdd, mulWordAfterAdd, inner, saved] using hrunToDouble)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned] using hrun)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, State.fork] using hnp)
  have hdouble := BigHelpers.gasSteps_addMaskedMod afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved
    (by simp [saved, mulWordRest]; omega) hcount
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hdouble' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry afterAdd (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 401) saved) afterDouble := by
    exact Challenge.EvmProof.GasSteps.cast hdouble rfl (by
      simp [afterDouble, mulWordAfterDouble, afterAdd, saved])
  have hrunNext := run_mulWordDoubleToNext current word a b out modulus count i j
    returnDest rest hcapAdd (by omega) hcode hrun
  have hnext := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulDoubleToNextPath (s := afterDouble)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned,
        Artifact.referenceArtifact] using hcode)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterDouble] using hrunNext)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned] using hrun)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned, State.fork] using hnp)
  exact hguard.trans <| htoAdd.trans <| hadd'.trans <|
    htoDouble.trans <| hdouble'.trans hnext

def gasSteps_mulWordLoop (current : State) (word a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulInnerState current word a b out modulus count i 0 returnDest rest)
      (mulInnerState
        (mulWordProgress current word a b out modulus count i returnDest rest 256)
        word a b out modulus count i 256 returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded 256 fun j hj =>
    gasSteps_mulWordBitIteration
      (mulWordProgress current word a b out modulus count i returnDest rest j)
      word a b out modulus count i j returnDest rest hcap hcount hj
      (by simpa using hcode)
      (by simpa [State.fork] using hfork)
      (by simpa using hrun)
      (by simpa [State.fork] using hnp)

def gasSteps_mulOuterGuardSegment (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulOuterState current a b out modulus count i returnDest rest)
      (mulOuterBody current a b out modulus count i returnDest rest) := by
  exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulOuterGuardPath
      (by simpa [mulOuterState, Artifact.referenceArtifact] using hcode)
      (by simpa [mulOuterState, State.fork] using hfork)
      (run_mulOuterGuard current a b out modulus count i returnDest rest
        (by omega) hcount hi hrun)
      (by simpa [mulOuterState] using hrun)
      (by simpa [mulOuterState, State.fork] using hnp)

def gasSteps_mulOuterLoadSegment (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulOuterBody current a b out modulus count i returnDest rest)
      (mulInnerLoop current a b out modulus count i 0 returnDest rest) := by
  exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulOuterLoadPath
      (by simpa [mulOuterBody, Artifact.referenceArtifact] using hcode)
      (by simpa [mulOuterBody, State.fork] using hfork)
      (run_mulOuterLoad current a b out modulus count i returnDest rest
        (by omega) (by omega) hrun)
      (by simpa [mulOuterBody] using hrun)
      (by simpa [mulOuterBody, State.fork] using hnp)

def gasSteps_mulInnerFinishSegment (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let inner := mulInnerState current word a b out modulus count i 256
      returnDest rest
    Challenge.EvmProof.GasSteps inner { inner with pc := UInt256.ofNat 413 } := by
  dsimp only
  exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulInnerGuardPath
      (by simpa [mulInnerState, Artifact.referenceArtifact] using hcode)
      (by simpa [mulInnerState, State.fork] using hfork)
      (run_mulWordInnerFinishGuard current word a b out modulus count i
        returnDest rest (by omega) hcode hrun)
      (by simpa [mulInnerState] using hrun)
      (by simpa [mulInnerState, State.fork] using hnp)

def gasSteps_mulInnerExitSegment (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let inner := mulInnerState current word a b out modulus count i 256
      returnDest rest
    Challenge.EvmProof.GasSteps { inner with pc := UInt256.ofNat 413 }
      (mulOuterNext inner a b out modulus count i returnDest rest) := by
  dsimp only
  exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulInnerToOuterPath
      (by simpa [mulInnerState, Artifact.referenceArtifact] using hcode)
      (by simpa [mulInnerState, State.fork] using hfork)
      (run_mulWordInnerToOuter current word a b out modulus count i
        returnDest rest (by omega) (by omega) hcode hrun)
      (by simpa [mulInnerState] using hrun)
      (by simpa [mulInnerState, State.fork] using hnp)

def gasSteps_mulOuterIteration (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let before := mulOuterProgress current a b out modulus count returnDest rest i
    Challenge.EvmProof.GasSteps
      (mulOuterState before a b out modulus count i returnDest rest)
      (mulOuterState
        (mulOuterProgress current a b out modulus count returnDest rest (i + 1))
        a b out modulus count (i + 1) returnDest rest) := by
  dsimp only
  let before := mulOuterProgress current a b out modulus count returnDest rest i
  let loaded := mulLoadedState before b i
  let word := mulLoadedWord before b i
  let afterWord := mulWordProgress loaded word a b out modulus count i
    returnDest rest 256
  change Challenge.EvmProof.GasSteps
    (mulOuterState before a b out modulus count i returnDest rest)
    (mulOuterState afterWord a b out modulus count (i + 1) returnDest rest)
  have hguard := gasSteps_mulOuterGuardSegment before a b out modulus count i
    returnDest rest hcap hcount hi
    (by simpa [before] using hcode)
    (by simpa [before, State.fork] using hfork)
    (by simpa [before] using hrun)
    (by simpa [before, State.fork] using hnp)
  have hloadRaw := gasSteps_mulOuterLoadSegment before a b out modulus count i
    returnDest rest hcap hcount hi
    (by simpa [before] using hcode)
    (by simpa [before, State.fork] using hfork)
    (by simpa [before] using hrun)
    (by simpa [before, State.fork] using hnp)
  have hload : Challenge.EvmProof.GasSteps
      (mulOuterBody before a b out modulus count i returnDest rest)
      (mulInnerState loaded word a b out modulus count i 0 returnDest rest) := by
    exact Challenge.EvmProof.GasSteps.cast hloadRaw rfl (by
      simp only [loaded, word, mulInnerLoop_eq_state])
  have hword := gasSteps_mulWordLoop loaded word a b out modulus count i
    returnDest rest hcap hcount
    (by simpa [loaded, mulLoadedState, before] using hcode)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [loaded, mulLoadedState, before] using hrun)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hnp)
  have hfinish := gasSteps_mulInnerFinishSegment afterWord word a b out modulus
    count i returnDest rest hcap
    (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [afterWord, loaded, mulLoadedState, before] using hrun)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hnp)
  have hexit := gasSteps_mulInnerExitSegment afterWord word a b out modulus
    count i returnDest rest hcap hcount hi
    (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [afterWord, loaded, mulLoadedState, before] using hrun)
    (by simpa [afterWord, loaded, mulLoadedState, before, State.fork] using hnp)
  have hchain := hguard.trans (hload.trans (hword.trans (hfinish.trans hexit)))
  exact Challenge.EvmProof.GasSteps.cast hchain rfl
    (mulOuterNext_innerState afterWord word a b out modulus count i returnDest rest)

def gasSteps_mulOuterLoop (current : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulOuterState current a b out modulus count 0 returnDest rest)
      (mulOuterState
        (mulOuterProgress current a b out modulus count returnDest rest count)
        a b out modulus count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_mulOuterIteration current a b out modulus count i returnDest rest
      hcap hcount hi hcode hfork hrun hnp

def gasSteps_mulFinish (current : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (mulOuterState current a b out modulus count count returnDest rest)
      (mulReturned current returnDest rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulOuterGuardPath
      (by simpa [mulOuterState, Artifact.referenceArtifact] using hcode)
      (by simpa [mulOuterState, State.fork] using hfork)
      (run_mulOuterFinishGuard current a b out modulus count returnDest rest
        (by omega) hcount hcode hrun)
      (by simpa [mulOuterState] using hrun)
      (by simpa [mulOuterState, State.fork] using hnp)
  have hexit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulOuterExitPath
      (by simpa [mulOuterState, Artifact.referenceArtifact] using hcode)
      (by simpa [mulOuterState, State.fork] using hfork)
      (run_mulOuterExit current a b out modulus count returnDest rest (by omega)
        hcode hrun hvalid)
      (by simpa [mulOuterState] using hrun)
      (by simpa [mulOuterState, State.fork] using hnp)
  exact hguard.trans hexit

theorem mulAfterBitDouble_represents (current : State) (a b : UInt256)
    (count i j acc addend modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (_hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let doubled := mulAfterBitDouble current a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count i j returnDest rest
    let bit := (mulBit current b i j).toNat
    Limbs.Represents doubled.memory 3072 count
        ((acc + bit * addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 4096 count
        ((addend + addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 0 count modulusValue := by
  let inner := mulInnerLoop current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let bitWord := mulBit current b i j
  let bit := bitWord.toNat
  let saved := mulBitRest current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let afterAdd := mulAfterBitAdd current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let doubled := mulAfterBitDouble current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  have hbitLe : bit ≤ 1 := mulBit_toNat_le_one current b i j
  have hbitWord : bitWord = UInt256.ofNat bit :=
    Challenge.EvmProof.Word.word_eq_ofNat_toNat bitWord
  have hfit0 : 0 + 32 * count < 2 ^ 256 := by omega
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit5120 : 5120 + 32 * count < 2 ^ 256 := by omega
  have hinnerAcc : Limbs.Represents inner.memory 3072 count acc := by
    simpa [inner, mulInnerLoop] using hacc
  have hinnerAddend : Limbs.Represents inner.memory 4096 count addend := by
    simpa [inner, mulInnerLoop] using haddend
  have hinnerModulus : Limbs.Represents inner.memory 0 count modulusValue := by
    simpa [inner, mulInnerLoop] using hmodulus
  have hafterAcc : Limbs.Represents afterAdd.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    simpa [afterAdd, mulAfterBitAdd, inner, bitWord, saved, hbitWord] using
      BigHelpers.addReturned_represents_mod inner 3072 4096 0 count bit
      acc addend modulusValue (UInt256.ofNat 383) saved hbitLe hfit3072
      hfit4096 hfit0 hfit5120 (by right; left; omega) (by right; omega)
      (by left; omega) (by left; omega) hinnerAcc hinnerAddend
      hinnerModulus haccReduced haddendReduced.le hmodulusBound
  have hafterAddend : Limbs.Represents afterAdd.memory 4096 count addend := by
    simpa [afterAdd, mulAfterBitAdd, inner, bitWord, saved, hbitWord] using
      BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 4096
      count addend (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by left; omega) (by left; omega) hinnerAddend
  have hafterModulus :
      Limbs.Represents afterAdd.memory 0 count modulusValue := by
    simpa [afterAdd, mulAfterBitAdd, inner, bitWord, saved, hbitWord] using
      BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 0
      count modulusValue (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by right; omega) (by left; omega) hinnerModulus
  have hdoubleAddend : Limbs.Represents doubled.memory 4096 count
      ((addend + addend) % modulusValue) := by
    simpa [doubled, mulAfterBitDouble, afterAdd] using
      BigHelpers.addReturned_represents_mod afterAdd 4096 4096 0 count 1
      addend addend modulusValue (UInt256.ofNat 401) saved (by omega)
      hfit4096 hfit4096 hfit0 hfit5120 (by left; rfl) (by right; omega)
      (by left; omega) (by left; omega) hafterAddend hafterAddend
      hafterModulus haddendReduced haddendReduced.le hmodulusBound
  have hdoubleAcc : Limbs.Represents doubled.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 3072
      count ((acc + bit * addend) % modulusValue) (UInt256.ofNat 401) saved
      hfit4096 hfit5120 (by right; omega) (by left; omega) hafterAcc
  have hdoubleModulus :
      Limbs.Represents doubled.memory 0 count modulusValue := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 0
      count modulusValue (UInt256.ofNat 401) saved hfit4096 hfit5120
      (by right; omega) (by left; omega) hafterModulus
  exact ⟨hdoubleAcc, hdoubleAddend, hdoubleModulus⟩

theorem mulWordAfterDouble_represents (current : State) (word a b : UInt256)
    (count i j acc addend modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (_hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let doubled := mulWordAfterDouble current word a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count i j returnDest rest
    let bit := (mulWordBit word j).toNat
    Limbs.Represents doubled.memory 3072 count
        ((acc + bit * addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 4096 count
        ((addend + addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 0 count modulusValue := by
  let inner := mulInnerState current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let bitWord := mulWordBit word j
  let bit := bitWord.toNat
  let saved := mulWordRest word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let afterAdd := mulWordAfterAdd current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let doubled := mulWordAfterDouble current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  have hbitLe : bit ≤ 1 := mulWordBit_toNat_le_one word j
  have hbitWord : bitWord = UInt256.ofNat bit :=
    Challenge.EvmProof.Word.word_eq_ofNat_toNat bitWord
  have hfit0 : 0 + 32 * count < 2 ^ 256 := by omega
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit5120 : 5120 + 32 * count < 2 ^ 256 := by omega
  have hinnerAcc : Limbs.Represents inner.memory 3072 count acc := by
    simpa [inner, mulInnerState] using hacc
  have hinnerAddend : Limbs.Represents inner.memory 4096 count addend := by
    simpa [inner, mulInnerState] using haddend
  have hinnerModulus : Limbs.Represents inner.memory 0 count modulusValue := by
    simpa [inner, mulInnerState] using hmodulus
  have hafterAcc : Limbs.Represents afterAdd.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    simpa [afterAdd, mulWordAfterAdd, inner, bitWord, saved, hbitWord] using
      BigHelpers.addReturned_represents_mod inner 3072 4096 0 count bit
      acc addend modulusValue (UInt256.ofNat 383) saved hbitLe hfit3072
      hfit4096 hfit0 hfit5120 (by right; left; omega) (by right; omega)
      (by left; omega) (by left; omega) hinnerAcc hinnerAddend
      hinnerModulus haccReduced haddendReduced.le hmodulusBound
  have hafterAddend : Limbs.Represents afterAdd.memory 4096 count addend := by
    simpa [afterAdd, mulWordAfterAdd, inner, bitWord, saved, hbitWord] using
      BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 4096
      count addend (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by left; omega) (by left; omega) hinnerAddend
  have hafterModulus :
      Limbs.Represents afterAdd.memory 0 count modulusValue := by
    simpa [afterAdd, mulWordAfterAdd, inner, bitWord, saved, hbitWord] using
      BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 0
      count modulusValue (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by right; omega) (by left; omega) hinnerModulus
  have hdoubleAddend : Limbs.Represents doubled.memory 4096 count
      ((addend + addend) % modulusValue) := by
    simpa [doubled, mulWordAfterDouble, afterAdd] using
      BigHelpers.addReturned_represents_mod afterAdd 4096 4096 0 count 1
      addend addend modulusValue (UInt256.ofNat 401) saved (by omega)
      hfit4096 hfit4096 hfit0 hfit5120 (by left; rfl) (by right; omega)
      (by left; omega) (by left; omega) hafterAddend hafterAddend
      hafterModulus haddendReduced haddendReduced.le hmodulusBound
  have hdoubleAcc : Limbs.Represents doubled.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 3072
      count ((acc + bit * addend) % modulusValue) (UInt256.ofNat 401) saved
      hfit4096 hfit5120 (by right; omega) (by left; omega) hafterAcc
  have hdoubleModulus :
      Limbs.Represents doubled.memory 0 count modulusValue := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 0
      count modulusValue (UInt256.ofNat 401) saved hfit4096 hfit5120
      (by right; omega) (by left; omega) hafterModulus
  exact ⟨hdoubleAcc, hdoubleAddend, hdoubleModulus⟩

theorem mulWordAfterDouble_preserves_region (current : State)
    (word a b : UInt256) (count i j ptr value : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents current.memory ptr count value) :
    Limbs.Represents
      (mulWordAfterDouble current word a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count i j returnDest rest).memory ptr count value := by
  let inner := mulInnerState current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let bitWord := mulWordBit word j
  let bit := bitWord.toNat
  let saved := mulWordRest word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let afterAdd := mulWordAfterAdd current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  have hbitWord : bitWord = UInt256.ofNat bit :=
    Challenge.EvmProof.Word.word_eq_ofNat_toNat bitWord
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit5120 : 5120 + 32 * count < 2 ^ 256 := by omega
  have hinnerRep : Limbs.Represents inner.memory ptr count value := by
    simpa [inner, mulInnerState] using hrep
  have hafterRep : Limbs.Represents afterAdd.memory ptr count value := by
    simpa [afterAdd, mulWordAfterAdd, inner, bitWord, saved, hbitWord] using
      BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 ptr
        count value (UInt256.ofNat 383) saved hfit3072 hfit5120 hptrOut
        hptrCandidate hinnerRep
  simpa [mulWordAfterDouble, afterAdd, saved] using
    BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 ptr
      count value (UInt256.ofNat 401) saved hfit4096 hfit5120 hptrAddend
      hptrCandidate hafterRep

theorem mulWordProgress_preserves_region (current : State)
    (word a b : UInt256) (count i steps ptr value : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hsteps : steps ≤ 256)
    (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents current.memory ptr count value) :
    Limbs.Represents
      (mulWordProgress current word a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count i returnDest rest steps).memory ptr count value := by
  induction steps with
  | zero => simpa [mulWordProgress] using hrep
  | succ steps ih =>
      have hbefore := ih (by omega)
      simpa [mulWordProgress] using
        mulWordAfterDouble_preserves_region
          (mulWordProgress current word a b (UInt256.ofNat 3072)
            (UInt256.ofNat 0) count i returnDest rest steps)
          word a b count i steps ptr value returnDest rest hcount hptrOut
          hptrAddend hptrCandidate hbefore

theorem mulWordProgress_represents (current : State) (word a b : UInt256)
    (count i steps acc addend modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hsteps : steps ≤ 256) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let progress := mulWordProgress current word a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count i returnDest rest steps
    let result := Algorithm.mulBits modulusValue acc addend
      (mulWordBits word steps)
    Limbs.Represents progress.memory 3072 count result.1 ∧
      Limbs.Represents progress.memory 4096 count result.2 ∧
      Limbs.Represents progress.memory 0 count modulusValue := by
  induction steps with
  | zero =>
      simp [mulWordProgress, mulWordBits, Algorithm.mulBits, hacc, haddend,
        hmodulus]
  | succ steps ih =>
      have hsteps' : steps ≤ 256 := by omega
      let before := mulWordProgress current word a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count i returnDest rest steps
      let beforeResult := Algorithm.mulBits modulusValue acc addend
        (mulWordBits word steps)
      have hbefore := ih hsteps'
      have hbeforeReduced := Algorithm.mulBits_lt (mulWordBits word steps)
        hmodulusPos haccReduced haddendReduced
      have hstep := mulWordAfterDouble_represents before word a b count i steps
        beforeResult.1 beforeResult.2 modulusValue returnDest rest hcount
        hmodulusPos hmodulusBound hbefore.1 hbefore.2.1 hbefore.2.2
        hbeforeReduced.1 hbeforeReduced.2
      simpa [mulWordProgress, mulWordBits, List.range_succ,
        List.map_append, Algorithm.mulBits_append, Algorithm.mulBits,
        before, beforeResult] using hstep

theorem mulOuterProgress_represents (current : State)
    (bPtr count steps acc addend bValue modulusValue : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hsteps : steps ≤ count)
    (hcount : count ≤ 32) (hbPtr : bPtr + 32 * count ≤ 3072)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hb : Limbs.Represents current.memory bPtr count bValue)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let progress := mulOuterProgress current (UInt256.ofNat 2048)
      (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count
      returnDest rest steps
    let result := Algorithm.mulBits modulusValue acc addend
      (mulOuterBits current.memory bPtr steps)
    Limbs.Represents progress.memory 3072 count result.1 ∧
      Limbs.Represents progress.memory 4096 count result.2 ∧
      Limbs.Represents progress.memory bPtr count bValue ∧
      Limbs.Represents progress.memory 0 count modulusValue := by
  induction steps with
  | zero =>
      simp [mulOuterProgress, mulOuterBits, Algorithm.mulBits, hacc, haddend,
        hb, hmodulus]
  | succ steps ih =>
      have hsteps' : steps ≤ count := by omega
      have hi : steps < count := by omega
      let before := mulOuterProgress current (UInt256.ofNat 2048)
        (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count
        returnDest rest steps
      let loaded := mulLoadedState before (UInt256.ofNat bPtr) steps
      let word := mulLoadedWord before (UInt256.ofNat bPtr) steps
      let beforeResult := Algorithm.mulBits modulusValue acc addend
        (mulOuterBits current.memory bPtr steps)
      have hbefore := ih hsteps'
      have hbeforeReduced := Algorithm.mulBits_lt
        (mulOuterBits current.memory bPtr steps) hmodulusPos haccReduced
        haddendReduced
      have hloadedAcc : Limbs.Represents loaded.memory 3072 count
          beforeResult.1 := by
        simpa [loaded, mulLoadedState] using hbefore.1
      have hloadedAddend : Limbs.Represents loaded.memory 4096 count
          beforeResult.2 := by
        simpa [loaded, mulLoadedState] using hbefore.2.1
      have hloadedB : Limbs.Represents loaded.memory bPtr count bValue := by
        simpa [loaded, mulLoadedState] using hbefore.2.2.1
      have hloadedModulus :
          Limbs.Represents loaded.memory 0 count modulusValue := by
        simpa [loaded, mulLoadedState] using hbefore.2.2.2
      have hwordAt : word =
          MachineState.readWord before.memory (bPtr + 32 * steps) := by
        have hfit : bPtr + 32 * steps < 2 ^ 256 := by omega
        have haddr :
            (UInt256.ofNat bPtr + UInt256.shiftLeft (UInt256.ofNat steps)
              (UInt256.ofNat 5)).toNat = bPtr + 32 * steps := by
          simpa [BigHelpers.clearOffset, add_comm] using
            BigHelpers.clearOffset_toNat bPtr steps hfit
        simp [word, mulLoadedWord, haddr]
      have hwordOriginal : word =
          MachineState.readWord current.memory (bPtr + 32 * steps) := by
        rw [hwordAt]
        exact readWord_eq_of_represents before.memory current.memory bPtr count
          bValue steps hi hbefore.2.2.1 hb
      have hwordProgress := mulWordProgress_represents loaded word
        (UInt256.ofNat 2048) (UInt256.ofNat bPtr) count steps 256
        beforeResult.1 beforeResult.2 modulusValue returnDest rest (by omega)
        hcount hmodulusPos hmodulusBound hloadedAcc hloadedAddend
        hloadedModulus hbeforeReduced.1 hbeforeReduced.2
      have hwordB := mulWordProgress_preserves_region loaded word
        (UInt256.ofNat 2048) (UInt256.ofNat bPtr) count steps 256 bPtr bValue
        returnDest rest (by omega) hcount (by right; omega) (by right; omega)
        (by left; omega) hloadedB
      let afterWord := mulWordProgress loaded word (UInt256.ofNat 2048)
        (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count
        steps returnDest rest 256
      let wordResult := Algorithm.mulBits modulusValue beforeResult.1
        beforeResult.2 (mulWordBits word 256)
      have hbits : mulOuterBits current.memory bPtr (steps + 1) =
          mulOuterBits current.memory bPtr steps ++ mulWordBits word 256 := by
        rw [mulOuterBits_succ, hwordOriginal]
      have hresult : Algorithm.mulBits modulusValue acc addend
          (mulOuterBits current.memory bPtr (steps + 1)) = wordResult := by
        rw [hbits, Algorithm.mulBits_append]
      have hwordProgress' :
          Limbs.Represents afterWord.memory 3072 count wordResult.1 ∧
            Limbs.Represents afterWord.memory 4096 count wordResult.2 ∧
            Limbs.Represents afterWord.memory 0 count modulusValue := by
        simpa only [afterWord, wordResult] using hwordProgress
      have hwordB' :
          Limbs.Represents afterWord.memory bPtr count bValue := by
        simpa only [afterWord] using hwordB
      change Limbs.Represents afterWord.memory 3072 count
          (Algorithm.mulBits modulusValue acc addend
            (mulOuterBits current.memory bPtr (steps + 1))).1 ∧
        Limbs.Represents afterWord.memory 4096 count
          (Algorithm.mulBits modulusValue acc addend
            (mulOuterBits current.memory bPtr (steps + 1))).2 ∧
        Limbs.Represents afterWord.memory bPtr count bValue ∧
        Limbs.Represents afterWord.memory 0 count modulusValue
      rw [hresult]
      exact ⟨hwordProgress'.1, hwordProgress'.2.1, hwordB',
        hwordProgress'.2.2⟩

theorem mulOuterProgress_count_represents_value (current : State)
    (bPtr count acc addend bValue modulusValue : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hbPtr : bPtr + 32 * count ≤ 3072)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hb : Limbs.Represents current.memory bPtr count bValue)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let progress := mulOuterProgress current (UInt256.ofNat 2048)
      (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count
      returnDest rest count
    Limbs.Represents progress.memory 3072 count
        ((acc + addend * bValue) % modulusValue) ∧
      Limbs.Represents progress.memory bPtr count bValue ∧
      Limbs.Represents progress.memory 0 count modulusValue := by
  let result := Algorithm.mulBits modulusValue acc addend
    (mulOuterBits current.memory bPtr count)
  have hprogress := mulOuterProgress_represents current bPtr count count acc
    addend bValue modulusValue returnDest rest (by omega) hcount hbPtr
    hmodulusPos hmodulusBound hacc haddend hb hmodulus haccReduced
    haddendReduced
  have hresultLt := Algorithm.mulBits_lt
    (mulOuterBits current.memory bPtr count) hmodulusPos haccReduced
    haddendReduced
  have hvalue := Algorithm.mulBits_fst modulusValue acc addend
    (mulOuterBits current.memory bPtr count)
  rw [Nat.mod_eq_of_lt hresultLt.1, value_mulOuterBits,
    Limbs.value_of_represents hb] at hvalue
  rw [← hvalue]
  exact ⟨hprogress.1, hprogress.2.2.1, hprogress.2.2.2⟩

theorem mulWordProgress_256_represents_value (current : State)
    (word a b : UInt256) (count i acc addend modulusValue : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let progress := mulWordProgress current word a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count i returnDest rest 256
    Limbs.Represents progress.memory 3072 count
        ((acc + addend * word.toNat) % modulusValue) ∧
      Limbs.Represents progress.memory 0 count modulusValue := by
  let result := Algorithm.mulBits modulusValue acc addend
    (mulWordBits word 256)
  have hprogress := mulWordProgress_represents current word a b count i 256
    acc addend modulusValue returnDest rest (by omega) hcount hmodulusPos
    hmodulusBound hacc haddend hmodulus haccReduced haddendReduced
  have hresultLt := Algorithm.mulBits_lt (mulWordBits word 256) hmodulusPos
    haccReduced haddendReduced
  have hvalue := Algorithm.mulBits_fst modulusValue acc addend
    (mulWordBits word 256)
  rw [Nat.mod_eq_of_lt hresultLt.1, value_mulWordBits] at hvalue
  rw [← hvalue]
  exact ⟨hprogress.1, hprogress.2.2⟩

theorem gasSteps_mulBitIteration_cost_potential (current : State)
    (a b out modulus : UInt256) (count i j : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulBitIteration current a b out modulus count i j returnDest rest
        hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (mulInnerLoop current a b out modulus count i j returnDest rest).activeWords.toNat =
      (426 + count * 906) + MachineState.memCost
        (mulInnerNext current a b out modulus count i j returnDest rest).activeWords.toNat := by
  let inner := mulInnerLoop current a b out modulus count i j returnDest rest
  let bit := mulBit current b i j
  let saved := mulBitRest current a b out modulus count i j returnDest rest
  let afterAdd := mulAfterBitAdd current a b out modulus count i j
    returnDest rest
  let afterDouble := mulAfterBitDouble current a b out modulus count i j
    returnDest rest
  have hsavedCap : saved.length < 1000 := by
    simp [saved, mulBitRest]
    omega
  have hcapAdd : rest.length < 1007 := by omega
  have hrunToDouble := run_mulAddToDouble current a b out modulus count i j
    returnDest rest hcapAdd hcode hrun
  have hrunNext := run_mulDoubleToNext current a b out modulus count i j
    returnDest rest hcapAdd (by omega) hcode hrun
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerGuardPath 26
      (run_mulInnerGuard current a b out modulus count i j returnDest rest
        (by omega) hj hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have htoAdd := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerToAddPath 44
      (run_mulInnerToAdd current a b out modulus count i j returnDest rest
        (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (by decide) (by decide)
  have hadd := BigHelpers.gasSteps_addMaskedMod_cost_potential inner out
    (UInt256.ofNat 4096) bit modulus count (UInt256.ofNat 383) saved
    hsavedCap hcount
    (by simpa [inner, mulInnerLoop] using hcode)
    (by simpa [inner, mulInnerLoop, State.fork] using hfork)
    (by simpa [inner, mulInnerLoop] using hrun)
    (by simpa [inner, mulInnerLoop, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have htoDouble :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      mulAddToDoublePath 30
      (by simpa [afterAdd, mulAfterBitAdd, inner, bit, saved] using
        hrunToDouble)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, State.fork] using hfork)
      (by decide) (by decide)
  have hdouble := BigHelpers.gasSteps_addMaskedMod_cost_potential afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved hsavedCap hcount
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hnext := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulDoubleToNextPath 28
      (by simpa [afterDouble] using hrunNext)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_mulBitIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [inner, bit, saved, afterAdd, afterDouble] at hguard htoAdd hadd htoDouble hdouble hnext
  simp only [mulAfterBitAdd, mulAfterBitDouble, mulInnerNext,
    BigHelpers.addEntry] at hguard htoAdd hadd htoDouble hdouble hnext ⊢
  omega

theorem gasSteps_mulWordBitIteration_cost_potential (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulWordBitIteration current word a b out modulus count i j
      returnDest rest hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (mulInnerState current word a b out modulus count i j
            returnDest rest).activeWords.toNat =
      (426 + count * 906) + MachineState.memCost
        (mulWordInnerNext current word a b out modulus count i j
          returnDest rest).activeWords.toNat := by
  let inner := mulInnerState current word a b out modulus count i j
    returnDest rest
  let bit := mulWordBit word j
  let saved := mulWordRest word a b out modulus count i j returnDest rest
  let afterAdd := mulWordAfterAdd current word a b out modulus count i j
    returnDest rest
  let afterDouble := mulWordAfterDouble current word a b out modulus count i j
    returnDest rest
  have hsavedCap : saved.length < 1000 := by
    simp [saved, mulWordRest]
    omega
  have hcapAdd : rest.length < 1007 := by omega
  have hrunToDouble := run_mulWordAddToDouble current word a b out modulus
    count i j returnDest rest hcapAdd hcode hrun
  have hrunNext := run_mulWordDoubleToNext current word a b out modulus count i j
    returnDest rest hcapAdd (by omega) hcode hrun
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerGuardPath 26
      (run_mulWordInnerGuard current word a b out modulus count i j returnDest
        rest (by omega) hj hrun)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (by decide) (by decide)
  have htoAdd := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerToAddPath 44
      (run_mulWordInnerToAdd current word a b out modulus count i j returnDest
        rest (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (by decide) (by decide)
  have hadd := BigHelpers.gasSteps_addMaskedMod_cost_potential inner out
    (UInt256.ofNat 4096) bit modulus count (UInt256.ofNat 383) saved
    hsavedCap hcount
    (by simpa [inner, mulInnerState] using hcode)
    (by simpa [inner, mulInnerState, State.fork] using hfork)
    (by simpa [inner, mulInnerState] using hrun)
    (by simpa [inner, mulInnerState, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have htoDouble :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      mulAddToDoublePath 30
      (by simpa [afterAdd, mulWordAfterAdd, inner, saved] using
        hrunToDouble)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, State.fork] using hfork)
      (by decide) (by decide)
  have hdouble := BigHelpers.gasSteps_addMaskedMod_cost_potential afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved hsavedCap hcount
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hnext := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulDoubleToNextPath 28
      (by simpa [afterDouble] using hrunNext)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_mulWordBitIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [inner, bit, saved, afterAdd, afterDouble] at hguard htoAdd hadd htoDouble hdouble hnext
  simp only [mulWordAfterAdd, mulWordAfterDouble, mulWordInnerNext,
    BigHelpers.addEntry] at hguard htoAdd hadd htoDouble hdouble hnext ⊢
  omega

theorem gasSteps_mulWordLoop_cost_potential (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulWordLoop current word a b out modulus count i returnDest rest
      hcap hcount hcode hfork hrun hnp).cost + MachineState.memCost
        (mulInnerState current word a b out modulus count i 0
          returnDest rest).activeWords.toNat =
      256 * (426 + count * 906) + MachineState.memCost
        (mulInnerState
          (mulWordProgress current word a b out modulus count i returnDest rest 256)
          word a b out modulus count i 256 returnDest rest).activeWords.toNat := by
  unfold gasSteps_mulWordLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro j hj
  simpa [mulWordInnerNext, mulWordProgress] using
    gasSteps_mulWordBitIteration_cost_potential
      (mulWordProgress current word a b out modulus count i returnDest rest j)
      word a b out modulus count i j returnDest rest hcap hcount hj
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)

/- Split into `BigMulGas` so the large execution certificate is opaque while
the aggregate cost proof is elaborated. -/
/-
private theorem telescope_outer_costs
    (guard load word finish exit p₀ p₁ p₂ p₃ p₄ p₅ work : Nat)
    (hguard : guard + p₀ = 26 + p₁)
    (hload : load + p₁ = 20 + p₂)
    (hword : word + p₂ = work + p₃)
    (hfinish : finish + p₃ = 26 + p₄)
    (hexit : exit + p₄ = 30 + p₅) :
    guard + (load + (word + (finish + exit))) + p₀ =
      (102 + work) + p₅ := by
  omega

theorem gasSteps_mulOuterIteration_cost_potential (current : State)
    (a b out modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    let before := mulOuterProgress current a b out modulus count returnDest rest i
    let after := mulOuterProgress current a b out modulus count returnDest rest (i + 1)
    (gasSteps_mulOuterIteration current a b out modulus count i returnDest rest
        hcap hcount hi hcode hfork hrun hnp).cost +
        MachineState.memCost
          (mulOuterState before a b out modulus count i returnDest rest).activeWords.toNat =
      (102 + 256 * (426 + count * 906)) + MachineState.memCost
        (mulOuterState after a b out modulus count (i + 1) returnDest rest).activeWords.toNat := by
  dsimp only
  let before := mulOuterProgress current a b out modulus count returnDest rest i
  let loaded := mulLoadedState before b i
  let word := mulLoadedWord before b i
  let afterWord := mulWordProgress loaded word a b out modulus count i
    returnDest rest 256
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterGuardPath 26
      (run_mulOuterGuard before a b out modulus count i returnDest rest
        (by omega) hcount hi (by simpa [before] using hrun))
      (by simpa [before, mulOuterState, State.fork] using hfork)
      (by decide) (by decide)
  have hload := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterLoadPath 20
      (run_mulOuterLoad before a b out modulus count i returnDest rest
        (by omega) (by omega) (by simpa [before] using hrun))
      (by simpa [before, mulOuterBody, State.fork] using hfork)
      (by decide) (by decide)
  have hword := gasSteps_mulWordLoop_cost_potential loaded word a b out modulus
    count i returnDest rest hcap hcount
    (by simpa [loaded, mulLoadedState, before] using hcode)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hfork)
    (by simpa [loaded, mulLoadedState, before] using hrun)
    (by simpa [loaded, mulLoadedState, before, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerGuardPath 26
      (run_mulWordInnerFinishGuard afterWord word a b out modulus count i
        returnDest rest (by omega)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hrun))
      (by simpa [afterWord, loaded, mulLoadedState, before, mulInnerState,
        State.fork] using hfork)
      (by decide) (by decide)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerToOuterPath 30
      (run_mulWordInnerToOuter afterWord word a b out modulus count i
        returnDest rest (by omega) (by omega)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hcode)
        (by simpa [afterWord, loaded, mulLoadedState, before] using hrun))
      (by simpa [afterWord, loaded, mulLoadedState, before, mulInnerState,
        State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_mulOuterIteration gasSteps_mulOuterGuardSegment
    gasSteps_mulOuterLoadSegment gasSteps_mulInnerFinishSegment
    gasSteps_mulInnerExitSegment
  simp only [id_eq]
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [before, loaded, word, afterWord] at hguard hload hword hfinish hexit
  simp only [mulOuterState, mulOuterBody, mulInnerLoop_eq_state,
    mulInnerState] at hguard hload hword hfinish hexit ⊢
  simp only [mulOuterProgress] at ⊢
  exact telescope_outer_costs _ _ _ _ _ _ _ _ _ _ _ _ hguard hload hword
    hfinish hexit

theorem gasSteps_mulOuterLoop_cost_potential (current : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulOuterLoop current a b out modulus count returnDest rest hcap
        hcount hcode hfork hrun hnp).cost + MachineState.memCost
          (mulOuterState current a b out modulus count 0 returnDest rest).activeWords.toNat =
      count * (102 + 256 * (426 + count * 906)) + MachineState.memCost
        (mulOuterState
          (mulOuterProgress current a b out modulus count returnDest rest count)
          a b out modulus count count returnDest rest).activeWords.toNat := by
  unfold gasSteps_mulOuterLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  simpa using gasSteps_mulOuterIteration_cost_potential current a b out modulus
    count i returnDest rest hcap hcount hi hcode hfork hrun hnp

theorem gasSteps_mulFinish_cost_potential (current : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      returnDest.toNat = true) :
    (gasSteps_mulFinish current a b out modulus count returnDest rest hcap
        hcount hcode hfork hrun hnp hvalid).cost + MachineState.memCost
          (mulOuterState current a b out modulus count count returnDest rest).activeWords.toNat =
      47 + MachineState.memCost
        (mulReturned current returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterGuardPath 26
      (run_mulOuterFinishGuard current a b out modulus count returnDest rest
        (by omega) hcount hcode hrun)
      (by simpa [mulOuterState, State.fork] using hfork)
      (by decide) (by decide)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulOuterExitPath 21
      (run_mulOuterExit current a b out modulus count returnDest rest (by omega)
        hcode hrun hvalid)
      (by simpa [mulOuterState, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_mulFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [mulOuterState, mulReturned] at hguard hexit ⊢
  omega

-/
theorem mulAfterCopy_represents (s : State) (bPtr count aValue bValue
    modulusValue : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcount : count ≤ 32) (hbPtr : bPtr + 32 * count ≤ 3072)
    (ha : Limbs.Represents s.memory 2048 count aValue)
    (hb : Limbs.Represents s.memory bPtr count bValue)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let copied := mulAfterCopy s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
      (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
    Limbs.Represents copied.memory 3072 count 0 ∧
      Limbs.Represents copied.memory 4096 count aValue ∧
      Limbs.Represents copied.memory bPtr count bValue ∧
      Limbs.Represents copied.memory 0 count modulusValue := by
  let cleared := mulAfterClear s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
    (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
  let copied := mulAfterCopy s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
    (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit2048 : 2048 + 32 * count < 2 ^ 256 := by omega
  have hclearedZero : Limbs.Represents cleared.memory 3072 count 0 := by
    exact BigHelpers.clearMemory_represents_zero s.memory 3072 count hfit3072
  have hclearedA : Limbs.Represents cleared.memory 2048 count aValue := by
    exact BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 2048
      count aValue hfit3072 (by right; omega) ha
  have hclearedB : Limbs.Represents cleared.memory bPtr count bValue := by
    exact BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 bPtr
      count bValue hfit3072 (by right; omega) hb
  have hclearedModulus :
      Limbs.Represents cleared.memory 0 count modulusValue := by
    exact BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 0
      count modulusValue hfit3072 (by right; omega) hmodulus
  have hcopiedAddend : Limbs.Represents copied.memory 4096 count aValue := by
    exact BigHelpers.copyMemory_represents cleared.memory 4096 2048 count aValue
      hclearedA hfit4096 hfit2048 (by right; omega)
  have hcopiedZero : Limbs.Represents copied.memory 3072 count 0 := by
    exact BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
      2048 3072 count 0 hfit4096 (by right; omega) hclearedZero
  have hcopiedB : Limbs.Represents copied.memory bPtr count bValue := by
    exact BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
      2048 bPtr count bValue hfit4096 (by right; omega) hclearedB
  have hcopiedModulus :
      Limbs.Represents copied.memory 0 count modulusValue := by
    exact BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
      2048 0 count modulusValue hfit4096 (by right; omega) hclearedModulus
  exact ⟨hcopiedZero, hcopiedAddend, hcopiedB, hcopiedModulus⟩

theorem mulOuterProgress_afterCopy_represents_product (s : State)
    (bPtr count aValue bValue modulusValue : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hbPtr : bPtr + 32 * count ≤ 3072) (hmodulusPos : 0 < modulusValue)
    (haReduced : aValue < modulusValue)
    (ha : Limbs.Represents s.memory 2048 count aValue)
    (hb : Limbs.Represents s.memory bPtr count bValue)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let copied := mulAfterCopy s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
      (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
    let progress := mulOuterProgress copied (UInt256.ofNat 2048)
      (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count
      returnDest rest count
    Limbs.Represents progress.memory 3072 count
        ((aValue * bValue) % modulusValue) ∧
      Limbs.Represents progress.memory bPtr count bValue ∧
      Limbs.Represents progress.memory 0 count modulusValue := by
  let copied := mulAfterCopy s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
    (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
  have hcopied := mulAfterCopy_represents s bPtr count aValue bValue
    modulusValue returnDest rest hcount hbPtr ha hb hmodulus
  have hproduct := mulOuterProgress_count_represents_value copied bPtr count
    0 aValue bValue modulusValue returnDest rest hcount hbPtr hmodulusPos
    hmodulus.1 hcopied.1 hcopied.2.1 hcopied.2.2.1 hcopied.2.2.2
    (by omega) haReduced
  simpa [Nat.zero_add] using hproduct

theorem mulReturned_represents_product (s : State)
    (bPtr count aValue bValue modulusValue : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hcount : count ≤ 32)
    (hbPtr : bPtr + 32 * count ≤ 3072) (hmodulusPos : 0 < modulusValue)
    (haReduced : aValue < modulusValue)
    (ha : Limbs.Represents s.memory 2048 count aValue)
    (hb : Limbs.Represents s.memory bPtr count bValue)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let copied := mulAfterCopy s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
      (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
    let progress := mulOuterProgress copied (UInt256.ofNat 2048)
      (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count
      returnDest rest count
    let returned := mulReturned progress returnDest rest
    Limbs.Represents returned.memory 3072 count
      ((aValue * bValue) % modulusValue) := by
  have hproduct := mulOuterProgress_afterCopy_represents_product s bPtr count
    aValue bValue modulusValue returnDest rest hcount hbPtr hmodulusPos
    haReduced ha hb hmodulus
  simpa [mulReturned] using hproduct.1

def gasSteps_mulInitialize (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulEntry s a b out modulus count returnDest rest)
      (mulOuterLoop s a b out modulus count 0 returnDest rest) := by
  let saved := [a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest
  have htoClear := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulToClearPath
      (by simpa [mulEntry, Artifact.referenceArtifact] using hcode)
      (by simpa [mulEntry, State.fork] using hfork)
      (run_mulToClear s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [mulEntry] using hrun)
      (by simpa [mulEntry, State.fork] using hnp)
  have hclear := BigHelpers.gasSteps_clear s out count (UInt256.ofNat 320)
    saved (by simp [saved]; omega) hcount hcode hfork hrun hnp (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 320 < 2 ^ 256)]
      exact jump320)
  have hclear' : Challenge.EvmProof.GasSteps
      (BigHelpers.clearEntry s out count (UInt256.ofNat 320) saved)
      (mulAfterClear s a b out modulus count returnDest rest) := by
    exact Challenge.EvmProof.GasSteps.cast hclear rfl (by
      simp [saved, mulAfterClear, BigHelpers.clearReturned])
  have htoCopy := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulToCopyPath
      (by simpa [mulAfterClear, Artifact.referenceArtifact] using hcode)
      (by simpa [mulAfterClear, State.fork] using hfork)
      (run_mulToCopy s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [mulAfterClear] using hrun)
      (by simpa [mulAfterClear, State.fork] using hnp)
  have hcopy := BigHelpers.gasSteps_copy
    (mulAfterClear s a b out modulus count returnDest rest)
    (UInt256.ofNat 4096) a count (UInt256.ofNat 333) saved
    (by simp [saved]; omega) hcount
    (by simpa [mulAfterClear] using hcode)
    (by simpa [mulAfterClear, State.fork] using hfork)
    (by simpa [mulAfterClear] using hrun)
    (by simpa [mulAfterClear, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 333 < 2 ^ 256)]
      exact jump333)
  have hcopy' : Challenge.EvmProof.GasSteps
      (BigHelpers.copyEntry (mulAfterClear s a b out modulus count
        returnDest rest) (UInt256.ofNat 4096) a count (UInt256.ofNat 333) saved)
      (mulAfterCopy s a b out modulus count returnDest rest) := by
    exact Challenge.EvmProof.GasSteps.cast hcopy rfl (by
      simp [saved, mulAfterCopy, mulAfterClear, BigHelpers.copyReturned])
  have hsetup := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka mulSetupPath
      (by simpa [mulAfterCopy, mulAfterClear,
        Artifact.referenceArtifact] using hcode)
      (by simpa [mulAfterCopy, mulAfterClear, State.fork] using hfork)
      (run_mulSetup s a b out modulus count returnDest rest (by omega) hrun)
      (by simpa [mulAfterCopy, mulAfterClear] using hrun)
      (by simpa [mulAfterCopy, mulAfterClear, State.fork] using hnp)
  exact htoClear.trans <| hclear'.trans <| htoCopy.trans <|
    hcopy'.trans hsetup

def gasSteps_mulModBig (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      returnDest.toNat = true) :
    let copied := mulAfterCopy s a b out modulus count returnDest rest
    let progress := mulOuterProgress copied a b out modulus count returnDest rest count
    Challenge.EvmProof.GasSteps
      (mulEntry s a b out modulus count returnDest rest)
      (mulReturned progress returnDest rest) := by
  dsimp only
  let copied := mulAfterCopy s a b out modulus count returnDest rest
  let progress := mulOuterProgress copied a b out modulus count returnDest rest count
  have hinit := gasSteps_mulInitialize s a b out modulus count returnDest rest
    (by omega) hcount hcode hfork hrun hnp
  have hinit' : Challenge.EvmProof.GasSteps
      (mulEntry s a b out modulus count returnDest rest)
      (mulOuterState copied a b out modulus count 0 returnDest rest) := by
    exact Challenge.EvmProof.GasSteps.cast hinit rfl (by
      simp [copied, mulOuterState, mulOuterLoop])
  have hloop := gasSteps_mulOuterLoop copied a b out modulus count returnDest
    rest hcap hcount
    (by simpa [copied, mulAfterCopy, mulAfterClear] using hcode)
    (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
    (by simpa [copied, mulAfterCopy, mulAfterClear] using hrun)
    (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hnp)
  have hfinish := gasSteps_mulFinish progress a b out modulus count returnDest
    rest hcap hcount
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear] using hcode)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear] using hrun)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear, State.fork] using hnp)
    hvalid
  exact hinit'.trans (hloop.trans hfinish)

theorem gasSteps_mulInitialize_cost_potential (s : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_mulInitialize s a b out modulus count returnDest rest hcap
      hcount hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      (138 + count * 158) + MachineState.memCost
        (mulOuterLoop s a b out modulus count 0 returnDest rest).activeWords.toNat := by
  let saved := [a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest
  let cleared := mulAfterClear s a b out modulus count returnDest rest
  let copied := mulAfterCopy s a b out modulus count returnDest rest
  have htoClear := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulToClearPath 21
      (run_mulToClear s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [mulEntry, State.fork] using hfork)
      (by decide) (by decide)
  have hclear := BigHelpers.gasSteps_clear_cost_potential s out count
    (UInt256.ofNat 320) saved (by simp [saved]; omega) hcount hcode hfork
    hrun hnp (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 320 < 2 ^ 256)]
      exact jump320)
  have htoCopy := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulToCopyPath 24
      (run_mulToCopy s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [cleared, mulAfterClear, State.fork] using hfork)
      (by decide) (by decide)
  have hcopy := BigHelpers.gasSteps_copy_cost_potential cleared
    (UInt256.ofNat 4096) a count (UInt256.ofNat 333) saved
    (by simp [saved]; omega) hcount
    (by simpa [cleared, mulAfterClear] using hcode)
    (by simpa [cleared, mulAfterClear, State.fork] using hfork)
    (by simpa [cleared, mulAfterClear] using hrun)
    (by simpa [cleared, mulAfterClear, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 333 < 2 ^ 256)]
      exact jump333)
  have hsetup := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulSetupPath 3
      (run_mulSetup s a b out modulus count returnDest rest (by omega) hrun)
      (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
      (by decide) (by decide)
  unfold gasSteps_mulInitialize
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [saved, cleared, copied] at htoClear hclear htoCopy hcopy hsetup
  simp only [mulEntry, BigHelpers.clearEntry, mulAfterClear,
    BigHelpers.clearReturned, BigHelpers.copyEntry, BigHelpers.copyReturned,
    mulAfterCopy, mulOuterLoop] at htoClear hclear htoCopy hcopy hsetup ⊢
  omega

/- Aggregate theorem is in `BigMulGas`. -/
/-
theorem gasSteps_mulModBig_cost_potential (s : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.referenceBytecode
      returnDest.toNat = true) :
    let copied := mulAfterCopy s a b out modulus count returnDest rest
    let progress := mulOuterProgress copied a b out modulus count returnDest rest count
    (gasSteps_mulModBig s a b out modulus count returnDest rest hcap hcount
        hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost s.activeWords.toNat =
      (185 + count * 158 +
          count * (102 + 256 * (426 + count * 906))) +
        MachineState.memCost (mulReturned progress returnDest rest).activeWords.toNat := by
  dsimp only
  let copied := mulAfterCopy s a b out modulus count returnDest rest
  let progress := mulOuterProgress copied a b out modulus count returnDest rest count
  have hinit := gasSteps_mulInitialize_cost_potential s a b out modulus count
    returnDest rest (by omega) hcount hcode hfork hrun hnp
  have hloop := gasSteps_mulOuterLoop_cost_potential copied a b out modulus count
    returnDest rest hcap hcount
    (by simpa [copied, mulAfterCopy, mulAfterClear] using hcode)
    (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
    (by simpa [copied, mulAfterCopy, mulAfterClear] using hrun)
    (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hnp)
  have hfinish := gasSteps_mulFinish_cost_potential progress a b out modulus count
    returnDest rest hcap hcount
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear] using hcode)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear] using hrun)
    (by simpa [progress, copied, mulAfterCopy, mulAfterClear, State.fork] using hnp)
    hvalid
  unfold gasSteps_mulModBig
  simp only [id_eq]
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  dsimp only [copied, progress] at hinit hloop hfinish
  simp only [mulOuterLoop, mulOuterState] at hinit hloop hfinish ⊢
  omega

-/
end Challenge.Modexp.Reference.Proofs.Bytecode.BigMul
