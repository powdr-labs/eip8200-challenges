import Challenge.Ripemd160.Reference.Proofs.Bytecode.PaddedBlockBridge

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Certified post-padding block driver

The reference bytecode at instruction indices 768--790 walks the padded
message in 64-byte blocks.  This file certifies the loop mechanics while
leaving the compression call as an explicit `GasSteps` seam.  Consequently
the driver can be composed with a compression proof without depending on its
internal state representation.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.DriverTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka

def setupPath : List Located :=
  [⟨768, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨769, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩]

def conditionPath : List Located :=
  [⟨770, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨771, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨772, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨773, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨774, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨775, .push ⟨2, by decide⟩ (UInt256.ofNat 0x64e), by rfl, by decide⟩,
   ⟨776, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def callPath : List Located :=
  [⟨777, .push ⟨2, by decide⟩ (UInt256.ofNat 0x643), by rfl, by decide⟩,
   ⟨778, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨779, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨780, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨781, .push ⟨2, by decide⟩ (UInt256.ofNat 0x26d), by rfl, by decide⟩,
   ⟨782, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def incrementPath : List Located :=
  [⟨783, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨784, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨785, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨786, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨787, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨788, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨789, .push ⟨2, by decide⟩ (UInt256.ofNat 0x62e), by rfl, by decide⟩,
   ⟨790, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem pc768 : Artifact.referenceArtifact.instructionPC 768 = 0x62c := by decide
@[simp] private theorem pc769 : Artifact.referenceArtifact.instructionPC 769 = 0x62d := by decide
@[simp] private theorem pc770 : Artifact.referenceArtifact.instructionPC 770 = 0x62e := by decide
@[simp] private theorem pc771 : Artifact.referenceArtifact.instructionPC 771 = 0x62f := by decide
@[simp] private theorem pc772 : Artifact.referenceArtifact.instructionPC 772 = 0x630 := by decide
@[simp] private theorem pc773 : Artifact.referenceArtifact.instructionPC 773 = 0x631 := by decide
@[simp] private theorem pc774 : Artifact.referenceArtifact.instructionPC 774 = 0x632 := by decide
@[simp] private theorem pc775 : Artifact.referenceArtifact.instructionPC 775 = 0x633 := by decide
@[simp] private theorem pc776 : Artifact.referenceArtifact.instructionPC 776 = 0x636 := by decide
@[simp] private theorem pc777 : Artifact.referenceArtifact.instructionPC 777 = 0x637 := by decide
@[simp] private theorem pc778 : Artifact.referenceArtifact.instructionPC 778 = 0x63a := by decide
@[simp] private theorem pc779 : Artifact.referenceArtifact.instructionPC 779 = 0x63b := by decide
@[simp] private theorem pc780 : Artifact.referenceArtifact.instructionPC 780 = 0x63e := by decide
@[simp] private theorem pc781 : Artifact.referenceArtifact.instructionPC 781 = 0x63f := by decide
@[simp] private theorem pc782 : Artifact.referenceArtifact.instructionPC 782 = 0x642 := by decide
@[simp] private theorem pc783 : Artifact.referenceArtifact.instructionPC 783 = 0x643 := by decide
@[simp] private theorem pc784 : Artifact.referenceArtifact.instructionPC 784 = 0x644 := by decide
@[simp] private theorem pc785 : Artifact.referenceArtifact.instructionPC 785 = 0x646 := by decide
@[simp] private theorem pc786 : Artifact.referenceArtifact.instructionPC 786 = 0x647 := by decide
@[simp] private theorem pc787 : Artifact.referenceArtifact.instructionPC 787 = 0x648 := by decide
@[simp] private theorem pc788 : Artifact.referenceArtifact.instructionPC 788 = 0x649 := by decide
@[simp] private theorem pc789 : Artifact.referenceArtifact.instructionPC 789 = 0x64a := by decide
@[simp] private theorem pc790 : Artifact.referenceArtifact.instructionPC 790 = 0x64d := by decide

def blockCount (input : ByteArray) : Nat :=
  Padding.paddedLength input.size / 64

def blockOffset (i : Nat) : Nat := i * 64

def blockOffsetWord (i : Nat) : UInt256 := UInt256.ofNat (blockOffset i)

def messageOffsetWord (i : Nat) : UInt256 :=
  UInt256.ofNat (Padding.messageOffset + blockOffset i)

def setupEntry (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 0x62c
    stack := [Padding.paddedWord input] }

def loopAt (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x62e
    stack := [blockOffsetWord i, Padding.paddedWord input] }

def afterCondition (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x637
    stack := [blockOffsetWord i, Padding.paddedWord input] }

/-- State at the compression entry point. The helper receives the concrete
padded-message pointer, its return destination, and the driver invariant
stack underneath. -/
def compressEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x26d
    stack := [messageOffsetWord i, UInt256.ofNat 0x643,
      blockOffsetWord i, Padding.paddedWord input] }

/-- Normalize an arbitrary post-compression state to the driver's return seam. -/
def compressReturned (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x643
    stack := [blockOffsetWord i, Padding.paddedWord input] }

def afterIteration (s : State) (input : ByteArray) (i : Nat) : State :=
  loopAt s input (i + 1)

def afterExit (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 0x64e
    stack := [blockOffsetWord (blockCount input), Padding.paddedWord input] }

theorem paddedLength_eq_blockCount (input : ByteArray) :
    Padding.paddedLength input.size = blockCount input * 64 := by
  exact Padding.paddedLength_eq_blocks input.size

private theorem paddedLength_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) :
    Padding.paddedLength input.size < 2 ^ 256 := by
  have hlt := Padding.paddedLength_lt input.size
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num at hfit ⊢
  omega

private theorem blockOffset_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i ≤ blockCount input) : blockOffset i < 2 ^ 256 := by
  have hpadded := paddedLength_lt_uint256 input hfit
  have heq := paddedLength_eq_blockCount input
  unfold blockOffset
  omega

private theorem messageOffset_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    Padding.messageOffset + blockOffset i < 2 ^ 256 := by
  have hpad := Padding.paddedLength_lt input.size
  have hoff : blockOffset i < Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num [Padding.messageOffset] at hfit ⊢
  omega

private theorem offset_lt_total (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    UInt256.lt (blockOffsetWord i) (Padding.paddedWord input) =
      UInt256.ofNat 1 := by
  have hoff := blockOffset_lt_uint256 input hfit i (Nat.le_of_lt hi)
  have hpad := paddedLength_lt_uint256 input hfit
  have hnat : blockOffset i < Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.lt blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad]
  simp only [if_pos hnat]

private theorem offset_not_lt_total (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) :
    UInt256.lt (blockOffsetWord (blockCount input))
      (Padding.paddedWord input) = 0 := by
  have hoff := blockOffset_lt_uint256 input hfit (blockCount input) (by omega)
  have hpad := paddedLength_lt_uint256 input hfit
  have heq : blockOffset (blockCount input) =
      Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    rfl
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.lt blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad, heq]
  simp only [Nat.lt_irrefl, if_false]
  rfl

/-- The driver's concrete pointer selects block `i` of the padded message. -/
theorem padReturned_messageBlockAt (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    ScheduleCorrect.MessageBlockAt (PaddingTrace.padReturned input).memory
      (messageOffsetWord i) (Padding.paddedMessage input) (blockOffset i) := by
  simpa [messageOffsetWord, blockOffset, blockCount] using
    PaddedBlockBridge.padReturned_blockIndexAt input hfit i hi

/-- The same block pointer is separated from the sixteen schedule slots. -/
theorem padReturned_blockSeparated (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord (messageOffsetWord i) k).toNat := by
  simpa [messageOffsetWord, blockOffset, blockCount] using
    PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i hi

theorem run_setup (s : State) (input : ByteArray)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPath (setupEntry s input) =
      some (loopAt s input 0) := by
  simp [setupPath, setupEntry, loopAt, blockOffsetWord, blockOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hrun]

theorem run_condition_continue (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath (loopAt s input i) =
      some (afterCondition s input i) := by
  have hlt := offset_lt_total input hfit i hi
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterCondition, hrun, hlt, hzero, hfalse]

theorem run_condition_exit (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (loopAt s input (blockCount input)) = some (afterExit s input) := by
  have hlt := offset_not_lt_total input hfit
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have honeNat : UInt256.toNat (1 : UInt256) = 1 := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 0x64e = true := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterExit, hrun, hcode, hlt, hzero,
    htrue, honeNat, UInt256.isTrue, hdest]

theorem run_call (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock callPath
      (afterCondition s input i) = some (compressEntry s input i) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (messageOffset_lt_uint256 input hfit i hi)
  have hdest : Decode.isValidJumpDest referenceBytecode 0x26d = true := by decide
  simp [callPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterCondition, compressEntry, messageOffsetWord, blockOffsetWord,
    hcode, hrun, hadd, hdest]

theorem run_increment (s : State) (input : ByteArray) (i : Nat)
    (hoff : blockOffset (i + 1) < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath
      (compressReturned s input i) = some (afterIteration s input i) := by
  have haddBound : i * 64 + 64 < 2 ^ 256 := by
    simpa [blockOffset, Nat.add_mul] using hoff
  have hadd : blockOffsetWord i + UInt256.ofNat 64 =
      blockOffsetWord (i + 1) := by
    simpa [blockOffsetWord, blockOffset, Nat.add_mul] using
      Challenge.EvmProof.Word.ofNat_add_ofNat
        (a := i * 64) (b := 64) haddBound
  have hdest : Decode.isValidJumpDest referenceBytecode 0x62e = true := by decide
  simp [incrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressReturned, afterIteration, loopAt,
    hcode, hrun, hadd, hdest, List.exchange]

private def gasStepsBlock (path : List Located) (s t : State)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path hcode hfork hresult hrun hnp

def gasSteps_setup (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (setupEntry s input) (loopAt s input 0) :=
  gasStepsBlock setupPath _ _ hcode hfork (run_setup s input hrun) hrun hnp

def gasSteps_condition_continue (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopAt s input i) (afterCondition s input i) :=
  gasStepsBlock conditionPath _ _ hcode hfork
    (run_condition_continue s input hfit i hi hrun) hrun hnp

def gasSteps_condition_exit (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopAt s input (blockCount input))
      (afterExit s input) :=
  gasStepsBlock conditionPath _ _ hcode hfork
    (run_condition_exit s input hfit hcode hrun) hrun hnp

def gasSteps_call (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (afterCondition s input i)
      (compressEntry s input i) :=
  gasStepsBlock callPath _ _ hcode hfork
    (run_call s input hfit i hi hcode hrun) hrun hnp

def gasSteps_increment (s : State) (input : ByteArray) (i : Nat)
    (hoff : blockOffset (i + 1) < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (compressReturned s input i)
      (afterIteration s input i) :=
  gasStepsBlock incrementPath _ _ hcode hfork
    (run_increment s input i hoff hcode hrun) hrun hnp

/-- One complete driver iteration, parameterized by the compression proof. -/
def gasSteps_iteration_of_compress (s next : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcodeS : s.executionEnv.code = referenceBytecode)
    (hforkS : s.fork = .Osaka) (hrunS : s.halt = .Running)
    (hnpS : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hcodeNext : next.executionEnv.code = referenceBytecode)
    (hforkNext : next.fork = .Osaka) (hrunNext : next.halt = .Running)
    (hnpNext : Precompile.isPrecompile next.executionEnv.fork
      next.executionEnv.codeAddr = false)
    (hcompress : Challenge.EvmProof.GasSteps (compressEntry s input i)
      (compressReturned next input i)) :
    Challenge.EvmProof.GasSteps (loopAt s input i)
      (afterIteration next input i) := by
  have hoff := blockOffset_lt_uint256 input hfit (i + 1) (by omega)
  exact (gasSteps_condition_continue s input hfit i hi hcodeS
      hforkS hrunS hnpS).trans
    ((gasSteps_call s input hfit i hi hcodeS hforkS hrunS hnpS).trans
      (hcompress.trans
        (gasSteps_increment next input i hoff hcodeNext hforkNext
          hrunNext hnpNext)))

/-- Iterate the driver over all padded blocks, given a state invariant family
and one compression certificate at each block. -/
def gasSteps_loop_of_compress (states : Nat → State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : ∀ i, i ≤ blockCount input →
      (states i).executionEnv.code = referenceBytecode)
    (hfork : ∀ i, i ≤ blockCount input → (states i).fork = .Osaka)
    (hrun : ∀ i, i ≤ blockCount input → (states i).halt = .Running)
    (hnp : ∀ i, i ≤ blockCount input →
      Precompile.isPrecompile (states i).executionEnv.fork
        (states i).executionEnv.codeAddr = false)
    (hcompress : ∀ i, i < blockCount input →
      Challenge.EvmProof.GasSteps (compressEntry (states i) input i)
        (compressReturned (states (i + 1)) input i)) :
    Challenge.EvmProof.GasSteps (loopAt (states 0) input 0)
      (loopAt (states (blockCount input)) input (blockCount input)) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => loopAt (states i) input i) (count := blockCount input)
  intro i hi
  simpa [afterIteration] using
    gasSteps_iteration_of_compress (states i) (states (i + 1)) input hfit i hi
      (hcode i (by omega)) (hfork i (by omega)) (hrun i (by omega))
      (hnp i (by omega)) (hcode (i + 1) (by omega))
      (hfork (i + 1) (by omega)) (hrun (i + 1) (by omega))
      (hnp (i + 1) (by omega)) (hcompress i hi)

end Challenge.Ripemd160.Reference.Proofs.Bytecode.DriverTrace
