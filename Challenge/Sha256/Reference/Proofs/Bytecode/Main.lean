import Challenge.Sha256.Reference.Proofs.Bytecode.Reference
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Direct execution of the SHA-256 main body

The first body block initializes the packed round constants and the eight hash
words. The proof below is parameterized over an arbitrary otherwise-unchanged
EVM state, so later blocks and participant proofs reuse the same three-opcode
`PUSH; PUSH; MSTORE` transformer.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

/-- Exact state transformer for one initialization store. -/
def applyInitStore (s : State) (w : Artifact.InitStore) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.instructionPC (w.index + 3))
    stack := []
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded w.value.toNat 32) w.offset.toNat
    activeWords := s.activeWordsAfterUInt256 w.offset.toNat 32 }

def gasSteps_initStore (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s (applyInitStore s w) := by
  have hv := Artifact.initStore_valid w hw
  have pcBound (i : Nat) : Artifact.instructionPC i < 2 ^ 256 := by
    have hle := Challenge.EvmProof.ProgramArtifact.instructionPC_le_code_size
      Artifact.referenceArtifact i
    change Artifact.instructionPC i ≤ referenceBytecode.size at hle
    rw [referenceBytecode_size] at hle
    omega
  have valuePos : 0 < w.valueWidth.val := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have offsetPos : 0 < w.offsetWidth.val := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have fitValue : w.value.toNat < 256 ^ w.valueWidth.val := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have fitOffset : w.offset.toNat < 256 ^ w.offsetWidth.val := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have pcToNat : s.pc.toNat = Artifact.instructionPC w.index := by
    rw [hpc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (pcBound w.index)]
  have decValue : s.decoded = some
      (.Push ⟨w.valueWidth⟩, some (w.value, w.valueWidth.val)) := by
    apply Challenge.EvmProof.ProgramArtifact.state_decoded_of
      Artifact.referenceArtifact s w.index
      (by simpa [Artifact.referenceArtifact] using hcode) pcToNat _ _
    · exact Artifact.decodeAt_push_index w.index w.valueWidth w.value hv.1 fitValue
    · simp only [Operation.availableInFork]
      rw [if_neg (by omega)]
  let s₁ : State := { s with
    stack := w.value :: s.stack
    pc := s.pc + UInt256.ofNat (w.valueWidth.val + 1) }
  have pc₁ : s₁.pc = UInt256.ofNat (Artifact.instructionPC (w.index + 1)) := by
    change s.pc + UInt256.ofNat (w.valueWidth.val + 1) = _
    rw [hpc]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by
      have := pcBound (w.index + 1)
      omega)]
    congr 1
    omega
  have g₁ : Challenge.EvmProof.GasSteps s s₁ := by
    apply Challenge.EvmProof.GasStep.pushN w.valueWidth w.value w.valueWidth.val
      valuePos
      decValue (by simp [hstack]) hrun hnp
  have pc₁ToNat : s₁.pc.toNat = Artifact.instructionPC (w.index + 1) := by
    rw [pc₁, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (pcBound (w.index + 1))]
  have decOffset : s₁.decoded = some
      (.Push ⟨w.offsetWidth⟩, some (w.offset, w.offsetWidth.val)) := by
    apply Challenge.EvmProof.ProgramArtifact.state_decoded_of
      Artifact.referenceArtifact s₁ (w.index + 1)
      (by simpa [Artifact.referenceArtifact, s₁] using hcode)
      pc₁ToNat _ _
    · exact Artifact.decodeAt_push_index (w.index + 1) w.offsetWidth w.offset
        hv.2.2.1 fitOffset
    · simp only [Operation.availableInFork]
      rw [if_neg (by omega)]
  let s₂ : State := { s₁ with
    stack := w.offset :: s₁.stack
    pc := s₁.pc + UInt256.ofNat (w.offsetWidth.val + 1) }
  have pc₂ : s₂.pc = UInt256.ofNat (Artifact.instructionPC (w.index + 2)) := by
    change s₁.pc + UInt256.ofNat (w.offsetWidth.val + 1) = _
    rw [pc₁]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by
      have := pcBound (w.index + 2)
      omega)]
    congr 1
    omega
  have g₂ : Challenge.EvmProof.GasSteps s₁ s₂ := by
    apply Challenge.EvmProof.GasStep.pushN w.offsetWidth w.offset w.offsetWidth.val
      offsetPos
      decOffset (by simp [s₁, hstack]) (by simpa [s₁] using hrun)
      (by simpa [s₁] using hnp)
  have pc₂ToNat : s₂.pc.toNat = Artifact.instructionPC (w.index + 2) := by
    rw [pc₂, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (pcBound (w.index + 2))]
  have decStore : s₂.decodedOp = some .MSTORE := by
    apply Challenge.EvmProof.ProgramArtifact.state_decodedOp_of
      Artifact.referenceArtifact s₂ (w.index + 2)
      (by simpa [Artifact.referenceArtifact, s₂, s₁] using hcode)
      pc₂ToNat .MSTORE none
    · exact Artifact.decodeAt_op_index (w.index + 2) .MSTORE hv.2.2.2.2.1
        (by decide) trivial
    · rfl
  have g₃ : Challenge.EvmProof.GasSteps s₂ (applyInitStore s w) := by
    have pc₃ : s₂.pc.succ = UInt256.ofNat (Artifact.instructionPC (w.index + 3)) := by
      rw [pc₂, Challenge.EvmProof.Word.succ_ofNat (by
        rw [← hv.2.2.2.2.2]
        exact pcBound (w.index + 3))]
      congr 1
      omega
    have gm := Challenge.EvmProof.GasStep.mstore (s := s₂) w.offset w.value []
      decStore (by simp [s₂, s₁, hstack])
      (by norm_num [s₂, s₁, hstack, Operation.pushArity, Operation.popArity])
      (by simpa [s₂, s₁] using hrun) (by simpa [s₂, s₁] using hnp)
    exact Challenge.EvmProof.GasSteps.cast gm rfl (by
      simp [applyInitStore, s₂, s₁, pc₃,
        State.activeWordsAfterUInt256])
  exact g₁.trans (g₂.trans g₃)

def InitChain : List Artifact.InitStore → Prop
  | [] | [_] => True
  | a :: b :: rest => b.index = a.index + 3 ∧ InitChain (b :: rest)

def gasSteps_initStores (s : State) :
    (ws : List Artifact.InitStore) →
    (∀ w, w ∈ ws → w ∈ Artifact.initStores) →
    InitChain ws →
    (∀ w, ws.head? = some w →
      s.pc = UInt256.ofNat (Artifact.instructionPC w.index)) →
    s.stack = [] →
    s.executionEnv.code = referenceBytecode →
    s.halt = .Running →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false →
    Challenge.EvmProof.GasSteps s (ws.foldl applyInitStore s)
  | [], _, _, _, _, _, _, _ => Challenge.EvmProof.GasSteps.refl s
  | [w], hmem, _, hpc, hstack, hcode, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      let gone := gasSteps_initStore s w hw hpcw hstack hcode hrun hnp
      exact Challenge.EvmProof.GasSteps.cast gone rfl (by simp)
  | w :: next :: rest, hmem, hchain, hpc, hstack, hcode, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      let gone := gasSteps_initStore s w hw hpcw hstack hcode hrun hnp
      have hnext : next.index = w.index + 3 := hchain.1
      have htail : InitChain (next :: rest) := hchain.2
      let grest := gasSteps_initStores (applyInitStore s w) (next :: rest)
        (fun x hx => hmem x (List.mem_cons_of_mem w hx))
        htail
        (fun x hx => by
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          simp [applyInitStore, hnext])
        (by simp [applyInitStore])
        (by simpa [applyInitStore] using hcode)
        (by simpa [applyInitStore] using hrun)
        (by simpa [applyInitStore] using hnp)
      let joined := gone.trans grest
      exact Challenge.EvmProof.GasSteps.cast joined rfl (by simp [List.foldl])

def initStart (calldata : ByteArray) : State :=
  { initialState referenceBytecode calldata 0 with
    pc := UInt256.ofNat (Artifact.instructionPC 659) }

def initializedState (calldata : ByteArray) : State :=
  Artifact.initStores.foldl applyInitStore (initStart calldata)

def gasSteps_mainJumpdest (calldata : ByteArray) :
    Challenge.EvmProof.GasSteps
      (Reference.atPC calldata Reference.mainPC) (initStart calldata) := by
  have hv := Artifact.mainEntry_valid
  have hd := Artifact.decodeAt_op_index 658 .JUMPDEST hv.2.1
    (by decide) trivial
  have g := Reference.gasSteps_jumpdest_at calldata Reference.mainPC (by
    simp [Reference.mainPC]) (by simpa [Reference.mainPC, hv.1] using hd)
  simpa [initStart, Reference.atPC, Reference.mainPC, hv.2.2] using g

def gasSteps_initialize (calldata : ByteArray) :
    Challenge.EvmProof.GasSteps
      (initialState referenceBytecode calldata 0) (initializedState calldata) := by
  have body := gasSteps_initStores (initStart calldata) Artifact.initStores
    (fun _ h => h) (by norm_num [InitChain, Artifact.initStores])
    (by
      intro w hw
      simp only [Artifact.initStores, List.head?_cons, Option.some.injEq] at hw
      subst w
      rfl)
    (by simp [initStart, initialState])
    (by simp [initStart, initialState])
    (by simp [initStart, initialState])
    (by simp [initStart, initialState, deployAddress_not_precompile])
  have body' : Challenge.EvmProof.GasSteps (initStart calldata)
      (initializedState calldata) :=
    Challenge.EvmProof.GasSteps.cast body rfl (by simp [initializedState])
  exact (Reference.gasSteps_to_main calldata).trans
    ((gasSteps_mainJumpdest calldata).trans body')

end Challenge.Sha256.Reference.Proofs.Bytecode.Main
