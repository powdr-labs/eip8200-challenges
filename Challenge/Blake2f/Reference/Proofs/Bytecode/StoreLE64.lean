import Challenge.Blake2f.Reference.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Direct trace of the compiled little-endian 64-bit writer

The helper is intentionally parameterized by its destination, value, return
address, and caller stack so candidate implementations can reuse its byte and
gas certificates.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.StoreLE64

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def initPath := Artifact.locatedPath [40, 41]
def testPath := Artifact.locatedPath [42, 43, 44, 45, 46, 47, 48]
def bodyPath := Artifact.locatedPath
  [49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
def exitPath := Artifact.locatedPath [67, 68, 69, 70, 71]

def wordByte (value : UInt256) (i : Nat) : UInt8 :=
  UInt8.ofNat ((UInt256.land
    (UInt256.shiftRight value (UInt256.ofNat (8 * i)))
    (UInt256.ofNat 0xff)).toNat % 256)

def writeByte (memory : ByteArray) (address : Nat) (value : UInt256)
    (i : Nat) : ByteArray :=
  MachineState.writeBytes memory (ByteArray.mk #[wordByte value i]) (address + i)

def writtenMemory (memory : ByteArray) (address : Nat) (value : UInt256) :
    Nat → ByteArray
  | 0 => memory
  | i + 1 => writeByte (writtenMemory memory address value i) address value i

def loopState (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 53
    stack := [UInt256.ofNat i, address, value, returnDest] ++ tail
    memory := writtenMemory s.memory address.toNat value i }

def finalState (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := tail
    memory := writtenMemory s.memory address.toNat value 8 }

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  by_cases hsize : size = 0
  · simp [hsize]
  · rw [if_neg hsize]
    apply Nat.max_eq_left
    have hcurr : 0 < curr := by omega
    have hdiv : (offset + size - 1) / 32 < curr := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, ofNat_toNat]

private theorem ofNatAdd (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

theorem run_init (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock initPath
      ({ s with
        pc := UInt256.ofNat 51
        stack := [address, value, returnDest] ++ tail }) =
      some (loopState s address value returnDest tail 0) := by
  have hcap3 : tail.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : tail.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hzeroStruct : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      initPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, writtenMemory, htail, hcap3, hcap4, hzeroStruct, hrun, ofNatAdd,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_test_continue (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock testPath
        (loopState s address value returnDest tail i) =
      some { loopState s address value returnDest tail i with
        pc := UInt256.ofNat 63 } := by
  have hcap4 : tail.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : tail.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap6 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hito : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpc56 : UInt256.ofNat 54 + UInt256.ofNat 2 = UInt256.ofNat 56 :=
    ofNatAdd 54 2 (by omega)
  have hpc62 : UInt256.ofNat 59 + UInt256.ofNat 3 = UInt256.ofNat 62 :=
    ofNatAdd 59 3 (by omega)
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      testPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, htail, hcap4, hcap5, hcap6, hi, hito, hpc56, hpc62,
      hrun, ofNatAdd,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_test_exit (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock testPath
        (loopState s address value returnDest tail 8) =
      some { loopState s address value returnDest tail 8 with
        pc := UInt256.ofNat 86 } := by
  have hcap4 : tail.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : tail.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap6 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc56 : UInt256.ofNat 54 + UInt256.ofNat 2 = UInt256.ofNat 56 :=
    ofNatAdd 54 2 (by omega)
  have hpc62 : UInt256.ofNat 59 + UInt256.ofNat 3 = UInt256.ofNat 62 :=
    ofNatAdd 59 3 (by omega)
  have h86 := Artifact.referenceArtifact.isValidJumpDest_index 67 (by rfl)
  have h86' : Decode.isValidJumpDest referenceBytecode 86 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h86
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      testPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, htail, hcap4, hcap5, hcap6, hpc56, hpc62,
      hrun, hcode, h86', ofNatAdd,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_body (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (haddress : address.toNat + 8 < 2 ^ 256)
    (hactive : address.toNat + 8 ≤ s.activeWords.toNat * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock bodyPath
        { loopState s address value returnDest tail i with pc := UInt256.ofNat 63 } =
      some (loopState s address value returnDest tail (i + 1)) := by
  have h53 := Artifact.referenceArtifact.isValidJumpDest_index 42 (by rfl)
  have h53' : Decode.isValidJumpDest referenceBytecode 53 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h53
  have hito : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 3) =
      UInt256.ofNat (8 * i) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by omega)]
    congr 1
    omega
  have hoffset : address + UInt256.ofNat i =
      UInt256.ofNat (address.toNat + i) := by
    have h := Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := address.toNat) (b := i) (by omega)
    rw [ofNat_toNat] at h
    exact h
  have hactive' :
      s.activeWordsAfterUInt256 (address.toNat + i) 1 = s.activeWords :=
    activeWordsAfterUInt256_eq s _ _ (by omega)
  have haddressI : address.toNat + i < 2 ^ 256 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hswap :
      ([UInt256.ofNat (i + 1), UInt256.ofNat i, address, value,
          returnDest] ++ tail).exchange 0 1 =
        some ([UInt256.ofNat i, UInt256.ofNat (i + 1), address, value,
          returnDest] ++ tail) := by rfl
  have hcap4 : tail.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : tail.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap6 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap7 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap8 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp_all (config := { maxSteps := 400000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      bodyPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, writtenMemory, writeByte, wordByte, htail,
      hcap4, hcap5, hcap6, hcap7, hcap8, hi, hito,
      hshift, hoffset, hactive', haddressI, hadd, hswap, hrun, hcode, h53',
      Nat.mod_eq_of_lt haddressI,
      ofNatAdd,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]
  rw [Nat.mod_eq_of_lt haddressI]
  exact ⟨hactive', rfl⟩

theorem run_exit (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock exitPath
        { loopState s address value returnDest tail 8 with pc := UInt256.ofNat 86 } =
      some (finalState s address value returnDest tail) := by
  have hcap1 : tail.length + 1 < 1024 := by omega
  have hcap2 : tail.length + 1 + 1 < 1024 := by omega
  have hcap3 : tail.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : tail.length + 1 + 1 + 1 + 1 < 1024 := by omega
  simp_all (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      exitPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, finalState, htail, hcap1, hcap2, hcap3, hcap4,
      hrun, hcode, hreturn, ofNatAdd,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

private def gasStepsBlock
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps a b := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact hresult
  · exact hrun
  · exact hnp

@[simp] private theorem gasStepsBlock_cost
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    (gasStepsBlock path hresult hcode hfork hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost path a := rfl

private theorem locatedCost_eq
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State} (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hfork : a.fork = .Osaka) (hactive : b.activeWords = a.activeWords)
    (hfree : ∀ located ∈ path,
      Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hwork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path a = work := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hwork
  rw [hactive] at hpotential
  omega

private theorem copyFree_of_all
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (hall : path.all
      (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true) :
    ∀ located ∈ path, Challenge.EvmProof.Meter.CopyFree located.instruction :=
  List.all_eq_true.mp hall

theorem init_cost (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running) (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost initPath
      ({ s with
        pc := UInt256.ofNat 51
        stack := [address, value, returnDest] ++ tail }) = 3 := by
  apply locatedCost_eq initPath 3
    (run_init s address value returnDest tail htail hrun)
    (by simpa [State.fork] using hfork) rfl
  · exact copyFree_of_all initPath (by decide)
  · decide

theorem test_continue_cost (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016) (hrun : s.halt = .Running)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost testPath
      (loopState s address value returnDest tail i) = 26 := by
  apply locatedCost_eq testPath 26
    (run_test_continue s address value returnDest tail i hi htail hrun)
    (by simpa [loopState, State.fork] using hfork) rfl
  · exact copyFree_of_all testPath (by decide)
  · decide

theorem test_exit_cost (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost testPath
      (loopState s address value returnDest tail 8) = 26 := by
  apply locatedCost_eq testPath 26
    (run_test_exit s address value returnDest tail htail hrun hcode)
    (by simpa [loopState, State.fork] using hfork) rfl
  · exact copyFree_of_all testPath (by decide)
  · decide

theorem body_cost (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (haddress : address.toNat + 8 < 2 ^ 256)
    (hactive : address.toNat + 8 ≤ s.activeWords.toNat * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost bodyPath
      { loopState s address value returnDest tail i with pc := UInt256.ofNat 63 } = 58 := by
  apply locatedCost_eq bodyPath 58
    (run_body s address value returnDest tail i hi htail hrun hcode
      haddress hactive)
    (by simpa [loopState, State.fork] using hfork) rfl
  · exact copyFree_of_all bodyPath (by decide)
  · decide

theorem exit_cost (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost exitPath
      { loopState s address value returnDest tail 8 with pc := UInt256.ofNat 86 } = 15 := by
  apply locatedCost_eq exitPath 15
    (run_exit s address value returnDest tail htail hrun hcode hreturn)
    (by simpa [loopState, State.fork] using hfork) rfl
  · exact copyFree_of_all exitPath (by decide)
  · decide

private def iterationGasSteps (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haddress : address.toNat + 8 < 2 ^ 256)
    (hactive : address.toNat + 8 ≤ s.activeWords.toNat * 32) :
    Challenge.EvmProof.GasSteps
      (loopState s address value returnDest tail i)
      (loopState s address value returnDest tail (i + 1)) := by
  exact (gasStepsBlock testPath
    (run_test_continue s address value returnDest tail i hi htail hrun)
    (by simpa [loopState] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (by simpa [loopState] using hrun)
    (by simpa [loopState] using hnp)).trans
    (gasStepsBlock bodyPath
      (run_body s address value returnDest tail i hi htail hrun hcode
        haddress hactive)
      (by simpa [loopState] using hcode)
      (by simpa [loopState, State.fork] using hfork)
      (by simpa [loopState] using hrun)
      (by simpa [loopState] using hnp))

@[simp] private theorem iterationGasSteps_cost (s : State)
    (address value returnDest : UInt256) (tail : List UInt256)
    (i : Nat) (hi : i < 8) (htail : tail.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haddress : address.toNat + 8 < 2 ^ 256)
    (hactive : address.toNat + 8 ≤ s.activeWords.toNat * 32) :
    (iterationGasSteps s address value returnDest tail i hi htail hcode hfork
      hrun hnp haddress hactive).cost = 84 := by
  unfold iterationGasSteps
  simp only [Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [test_continue_cost s address value returnDest tail i hi htail hrun hfork,
    body_cost s address value returnDest tail i hi htail hrun hcode hfork
      haddress hactive]

def gasSteps (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haddress : address.toNat + 8 < 2 ^ 256)
    (hactive : address.toNat + 8 ≤ s.activeWords.toNat * 32)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      ({ s with
        pc := UInt256.ofNat 51
        stack := [address, value, returnDest] ++ tail })
      (finalState s address value returnDest tail) := by
  have ginit := gasStepsBlock initPath
    (run_init s address value returnDest tail htail hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have gloop : Challenge.EvmProof.GasSteps
      (loopState s address value returnDest tail 0)
      (loopState s address value returnDest tail 8) :=
    Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
      (I := loopState s address value returnDest tail)
      (fun i hi => iterationGasSteps s address value returnDest tail i hi htail
        hcode hfork hrun hnp haddress hactive)
  have gtest := gasStepsBlock testPath
    (run_test_exit s address value returnDest tail htail hrun hcode)
    (by simpa [loopState] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (by simpa [loopState] using hrun) (by simpa [loopState] using hnp)
  have gexit := gasStepsBlock exitPath
    (run_exit s address value returnDest tail htail hrun hcode hreturn)
    (by simpa [loopState] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (by simpa [loopState] using hrun) (by simpa [loopState] using hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (ginit.trans (gloop.trans (gtest.trans gexit))) rfl rfl

@[simp] theorem gasSteps_cost (s : State) (address value returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haddress : address.toNat + 8 < 2 ^ 256)
    (hactive : address.toNat + 8 ≤ s.activeWords.toNat * 32)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (gasSteps s address value returnDest tail htail hcode hfork hrun hnp
      haddress hactive hreturn).cost = 716 := by
  unfold gasSteps
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost, gasStepsBlock_cost]
  rw [init_cost s address value returnDest tail htail hrun hfork,
    test_exit_cost s address value returnDest tail htail hrun hcode hfork,
    exit_cost s address value returnDest tail htail hrun hcode hfork hreturn]
  have hloop := Challenge.EvmProof.GasSteps.iterateBounded_cost_of_const
    8 84
    (fun i hi => iterationGasSteps s address value returnDest tail i hi htail
      hcode hfork hrun hnp haddress hactive)
    (fun i hi => iterationGasSteps_cost s address value returnDest tail i hi htail
      hcode hfork hrun hnp haddress hactive)
  rw [hloop]

end Challenge.Blake2f.Reference.Proofs.Bytecode.StoreLE64
