import Challenge.Sha256.Reference.Proofs.Bytecode
import Challenge.Sha256.Reference.Proofs.Bytecode.Artifact
import Challenge.Sha256.ProofSupport.InitialState
import EvmSemantics.EVM.StepDeterminism
set_option warningAsError true
set_option linter.dupNamespace false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Direct execution proof for the frozen SHA-256 reference bytecode

This module starts the concrete proof of `referenceDirectGoal`. Unlike the
verified-Yul proof, every transition here is a transition of the frozen bytes under
`EvmSemantics.EVM.stepF`; no Yul syntax or compiler theorem is in scope.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Reference

open EvmSemantics
open EvmSemantics.EVM

/-- The SHA program body starts after the compiler-generated function
trampolines. -/
def mainPC : Nat := 0x03e5

/-- Gas-erased reference state at a concrete program counter.  `GasSteps`
supplies the actual budget without duplicating otherwise identical states. -/
def atPC (calldata : ByteArray) (pc : Nat) : State :=
  { initialState referenceBytecode calldata 0 with pc := UInt256.ofNat pc }

def atPCStack (calldata : ByteArray) (pc : Nat) (stack : List UInt256) : State :=
  { initialState referenceBytecode calldata 0 with pc := UInt256.ofNat pc, stack }

@[simp] theorem withGas_atPC (calldata : ByteArray) (pc gas : Nat) :
    Challenge.EvmProof.withGas (atPC calldata pc) gas =
      { initialState referenceBytecode calldata gas with pc := UInt256.ofNat pc } := by
  rfl

def gasSteps_jumpdest_at (calldata : ByteArray) (pc : Nat)
    (hpc : pc + 1 < 2 ^ 256)
    (hdecode : Decode.decodeAt referenceBytecode pc = some (.JUMPDEST, none)) :
    Challenge.EvmProof.GasSteps (atPC calldata pc) (atPC calldata (pc + 1)) := by
  have hop : (atPC calldata pc).decodedOp = some .JUMPDEST := by
    unfold State.decodedOp
    have hd : (atPC calldata pc).decoded = some (.JUMPDEST, none) := by
      unfold State.decoded
      rw [show (atPC calldata pc).executionEnv.code = referenceBytecode by rfl]
      rw [show (atPC calldata pc).pc.toNat = pc by
        rw [show (atPC calldata pc).pc = UInt256.ofNat pc by rfl,
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : pc < 2 ^ 256)]]
      rw [hdecode]
      rfl
    rw [hd]
    rfl
  have hsucc := Challenge.EvmProof.Word.succ_ofNat hpc
  apply Challenge.EvmProof.GasStep.of_running 1 rfl deployAddress_not_precompile
  intro gas hgas
  have hstep := StepRunning.jumpdest
    (s := Challenge.EvmProof.withGas (atPC calldata pc) gas)
    hop (by simpa [atPC, initialState, State.fork, Gas.baseCost] using hgas)
    (by simp [Challenge.EvmProof.withGas, atPC, initialState,
      Operation.pushArity, Operation.popArity])
  simpa [Challenge.EvmProof.withGas, atPC, hsucc, Gas.baseCost] using hstep

def gasSteps_push2_at (calldata : ByteArray) (pc dest : Nat)
    (hpc : pc + 3 < 2 ^ 256)
    (hdecode : Decode.decodeAt referenceBytecode pc =
      some (.Push ⟨2, by decide⟩, some (UInt256.ofNat dest, 2))) :
    Challenge.EvmProof.GasSteps (atPC calldata pc)
      (atPCStack calldata (pc + 3) [UInt256.ofNat dest]) := by
  have hpcadd := Challenge.EvmProof.Word.ofNat_add_ofNat hpc
  apply Challenge.EvmProof.GasStep.of_running 3 rfl deployAddress_not_precompile
  intro gas hgas
  have hstep := StepRunning.pushN
    (s := Challenge.EvmProof.withGas (atPC calldata pc) gas)
    (k := ⟨2, by decide⟩) (data := UInt256.ofNat dest) (immWidth := 2)
    (by decide) (by
      unfold State.decoded
      rw [show (Challenge.EvmProof.withGas (atPC calldata pc) gas).executionEnv.code =
        referenceBytecode by rfl]
      rw [show (Challenge.EvmProof.withGas (atPC calldata pc) gas).pc.toNat = pc by
        rw [show (Challenge.EvmProof.withGas (atPC calldata pc) gas).pc =
          UInt256.ofNat pc by rfl,
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : pc < 2 ^ 256)]]
      rw [hdecode]
      rfl)
    (by simpa [atPC, initialState, State.fork, Gas.baseCost] using hgas)
    (by simp [Challenge.EvmProof.withGas, atPC, initialState])
  simpa [Challenge.EvmProof.withGas, atPC, atPCStack, hpcadd,
    initialState, Gas.baseCost] using hstep

def gasSteps_jump_at (calldata : ByteArray) (pc dest : Nat)
    (hpc : pc + 1 < 2 ^ 256)
    (hdest : dest < 2 ^ 256)
    (hdecode : Decode.decodeAt referenceBytecode pc = some (.JUMP, none))
    (hvalid : Decode.isValidJumpDest referenceBytecode dest = true) :
    Challenge.EvmProof.GasSteps
      (atPCStack calldata pc [UInt256.ofNat dest]) (atPC calldata dest) := by
  have hop : (atPCStack calldata pc [UInt256.ofNat dest]).decodedOp =
      some .JUMP := by
    unfold State.decodedOp
    have hd : (atPCStack calldata pc [UInt256.ofNat dest]).decoded =
        some (.JUMP, none) := by
      unfold State.decoded
      rw [show (atPCStack calldata pc [UInt256.ofNat dest]).executionEnv.code =
        referenceBytecode by rfl]
      rw [show (atPCStack calldata pc [UInt256.ofNat dest]).pc.toNat = pc by
        rw [show (atPCStack calldata pc [UInt256.ofNat dest]).pc =
          UInt256.ofNat pc by rfl,
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : pc < 2 ^ 256)]]
      rw [hdecode]
      rfl
    rw [hd]
    rfl
  apply Challenge.EvmProof.GasStep.of_running 8 rfl deployAddress_not_precompile
  intro gas hgas
  have hstep := StepRunning.jump
    (s := Challenge.EvmProof.withGas
      (atPCStack calldata pc [UInt256.ofNat dest]) gas)
    (dest := UInt256.ofNat dest) (rest := []) hop
    (by simpa [atPCStack, initialState, State.fork, Gas.baseCost] using hgas)
    (by simp [Challenge.EvmProof.withGas, atPCStack, initialState])
    (by
      change Decode.isValidJumpDest referenceBytecode
        (UInt256.ofNat dest).toNat = true
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hdest]
      exact hvalid)
    (by simp [Challenge.EvmProof.withGas, atPCStack, initialState,
      Operation.pushArity, Operation.popArity])
  simpa [Challenge.EvmProof.withGas, atPC, atPCStack, initialState,
    Gas.baseCost] using hstep

def gasSteps_trampoline (calldata : ByteArray) (src dest : Nat)
    (hsrc : src + 5 < 2 ^ 256) (hdest : dest < 2 ^ 256)
    (hjd : Decode.decodeAt referenceBytecode src = some (.JUMPDEST, none))
    (hpush : Decode.decodeAt referenceBytecode (src + 1) =
      some (.Push ⟨2, by decide⟩, some (UInt256.ofNat dest, 2)))
    (hjump : Decode.decodeAt referenceBytecode (src + 4) = some (.JUMP, none))
    (hvalid : Decode.isValidJumpDest referenceBytecode dest = true) :
    Challenge.EvmProof.GasSteps (atPC calldata src) (atPC calldata dest) := by
  exact (gasSteps_jumpdest_at calldata src (by omega) hjd).trans
    ((gasSteps_push2_at calldata (src + 1) dest (by omega) (by simpa using hpush)).trans
      (gasSteps_jump_at calldata (src + 4) dest (by omega) hdest
        (by simpa using hjump) hvalid))

/-- The compiler-generated entry chain. Every element is a `JUMPDEST`; all
but the last immediately push and jump to the next element. -/
def entryTargets : List Nat :=
  Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.entryTargets

def entryLinks : List (Nat × Nat) :=
  Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.entryTrampolines.map
    (fun t => (t.src, t.dest))

theorem reference_decode_entry_push :
    Decode.decodeAt referenceBytecode 0 =
      some (.Push ⟨2, by decide⟩, some (UInt256.ofNat 0x001b, 2)) := by
  have hv := Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.initialEntry_valid
  simpa [hv.1] using
    Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.decodeAt_push_index 0
      ⟨2, by decide⟩ (UInt256.ofNat 0x001b) hv.2.1 (by decide)

theorem reference_decode_entry_jump :
    Decode.decodeAt referenceBytecode 3 = some (.JUMP, none) := by
  have hv := Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.initialEntry_valid
  simpa [hv.2.2.1] using
    Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.decodeAt_op_index 1 .JUMP
      hv.2.2.2 (by decide) trivial

/-- Membership in the certified list yields the exact side condition used by
`JUMP` and `JUMPI`. -/
theorem reference_entryTarget_isValid {pc : Nat} (hpc : pc ∈ entryTargets) :
    Decode.isValidJumpDest referenceBytecode pc = true := by
  exact Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.entryTarget_isValid hpc

theorem reference_first_target_is_jumpdest :
    Decode.isValidJumpDest referenceBytecode 0x001b = true := by
  apply reference_entryTarget_isValid
  simp [entryTargets, Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.entryTargets]

theorem initialState_decoded_entry_push (calldata : ByteArray) (gas : Nat) :
    (initialState referenceBytecode calldata gas).decoded =
      some (.Push ⟨2, by decide⟩, some (UInt256.ofNat 0x001b, 2)) := by
  unfold State.decoded
  rw [show (initialState referenceBytecode calldata gas).executionEnv.code =
    referenceBytecode by rfl]
  rw [show (initialState referenceBytecode calldata gas).pc.toNat = 0 by rfl]
  rw [reference_decode_entry_push]
  rfl

theorem pushed_decoded_entry_jump (calldata : ByteArray) (gas : Nat) :
    ({ initialState referenceBytecode calldata gas with
      pc := UInt256.ofNat 3
      stack := [UInt256.ofNat 0x001b]
      gasAvailable := gas - 3 } : State).decodedOp = some .JUMP := by
  unfold State.decodedOp State.decoded
  rw [show ({ initialState referenceBytecode calldata gas with
    pc := UInt256.ofNat 3
    stack := [UInt256.ofNat 0x001b]
    gasAvailable := gas - 3 } : State).executionEnv.code = referenceBytecode by rfl]
  rw [show (UInt256.ofNat 3).toNat = 3 by decide]
  rw [reference_decode_entry_jump]
  rfl

theorem step_entry_push (calldata : ByteArray) (gas : Nat) (hgas : 3 ≤ gas) :
    Step (initialState referenceBytecode calldata gas)
      { initialState referenceBytecode calldata gas with
          pc := UInt256.ofNat 3
          stack := [UInt256.ofNat 0x001b]
          gasAvailable := gas - 3 } := by
  have hpc : (0 : UInt256) + UInt256.ofNat 3 = UInt256.ofNat 3 := by decide
  apply Step.running rfl deployAddress_not_precompile
  simpa [initialState, State.fork, Gas.baseCost, hpc] using
    StepRunning.pushN (s := initialState referenceBytecode calldata gas)
      (k := ⟨2, by decide⟩) (data := UInt256.ofNat 0x001b) (immWidth := 2)
      (by decide) (initialState_decoded_entry_push calldata gas)
      (by change 3 ≤ gas; exact hgas) (by simp [initialState])

theorem stepF_entry_push (calldata : ByteArray) (gas : Nat) (hgas : 3 ≤ gas) :
    stepF (initialState referenceBytecode calldata gas) =
      { initialState referenceBytecode calldata gas with
          pc := UInt256.ofNat 3
          stack := [UInt256.ofNat 0x001b]
          gasAvailable := gas - 3 } := by
  exact step_complete (step_entry_push calldata gas hgas)

theorem step_entry_jump (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    Step { initialState referenceBytecode calldata gas with
        pc := UInt256.ofNat 3
        stack := [UInt256.ofNat 0x001b]
        gasAvailable := gas - 3 }
      { initialState referenceBytecode calldata gas with
          pc := UInt256.ofNat 0x001b
          gasAvailable := gas - 11 } := by
  have hjump : 8 ≤ gas - 3 := by omega
  have hsub : gas - 3 - 8 = gas - 11 := by omega
  apply Step.running rfl deployAddress_not_precompile
  simpa [initialState, State.fork, Gas.baseCost, hsub] using
    StepRunning.jump
      (s := { initialState referenceBytecode calldata gas with
        pc := UInt256.ofNat 3
        stack := [UInt256.ofNat 0x001b]
        gasAvailable := gas - 3 })
      (dest := UInt256.ofNat 0x001b) (rest := [])
      (pushed_decoded_entry_jump calldata gas)
      (by change 8 ≤ gas - 3; exact hjump) (by simp) (by
        change Decode.isValidJumpDest referenceBytecode 0x001b = true
        exact reference_first_target_is_jumpdest) (by
          norm_num [Operation.pushArity, Operation.popArity])

theorem stepF_entry_jump (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    stepF { initialState referenceBytecode calldata gas with
        pc := UInt256.ofNat 3
        stack := [UInt256.ofNat 0x001b]
        gasAvailable := gas - 3 } =
      { initialState referenceBytecode calldata gas with
          pc := UInt256.ofNat 0x001b
          gasAvailable := gas - 11 } := by
  exact step_complete (step_entry_jump calldata gas hgas)

/-- The first executable direct-bytecode block consumes the initial `PUSH2; JUMP` and
lands on the first certified trampoline target. -/
theorem execN_to_firstTarget (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    Challenge.EvmProof.execN 2 (initialState referenceBytecode calldata gas) =
      { initialState referenceBytecode calldata gas with
          pc := UInt256.ofNat 0x001b
          gasAvailable := gas - 11 } := by
  have hpush : 3 ≤ gas := by omega
  simp [Challenge.EvmProof.execN, stepF_entry_push calldata gas hpush,
    stepF_entry_jump calldata gas hgas]

/-- Relational form of the first reference-bytecode block. Later block and
loop proofs compose this theorem with `Reaches.trans`. -/
theorem reaches_firstTarget (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    Challenge.EvmProof.Reaches
      (fun s => s = initialState referenceBytecode calldata gas)
      (fun s => s = { initialState referenceBytecode calldata gas with
        pc := UInt256.ofNat 0x001b
        gasAvailable := gas - 11 }) := by
  intro s hs
  subst s
  have hpush : 3 ≤ gas := by omega
  exact ⟨_, .trans (step_entry_push calldata gas hpush)
    (.trans (step_entry_jump calldata gas hgas) (.refl _)), rfl⟩

/-- Gas-parametric form of the first `PUSH2; JUMP`. -/
def gasSteps_to_firstTarget (calldata : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode calldata 0)
      (atPC calldata 0x001b) := by
  refine ⟨11, fun gas hgas => ?_⟩
  have hpush : 3 ≤ gas := by omega
  simpa [Challenge.EvmProof.withGas, atPC, initialState] using
    (Steps.trans (step_entry_push calldata gas hpush)
      (Steps.trans (step_entry_jump calldata gas hgas) (Steps.refl _)))

def gasSteps_entryTrampoline (calldata : ByteArray)
    (t : Artifact.EntryTrampoline) (ht : t ∈ Artifact.entryTrampolines) :
    Challenge.EvmProof.GasSteps (atPC calldata t.src) (atPC calldata t.dest) := by
  have hv := Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.entryTrampoline_valid t ht
  have hb : t.src + 5 < 2 ^ 256 ∧ t.dest < 2 ^ 256 := by
    simp only [Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.entryTrampolines,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp_all
  apply gasSteps_trampoline calldata t.src t.dest hb.1 hb.2
  · simpa [hv.1] using
      Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.decodeAt_op_index t.srcIndex .JUMPDEST
        hv.2.1 (by decide) trivial
  · have hfit : (UInt256.ofNat t.dest).toNat < 256 ^ 2 := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hb.2]
      simp only [Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.entryTrampolines,
        List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp_all
    simpa [hv.2.2.1] using
      Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.decodeAt_push_index (t.srcIndex + 1)
        ⟨2, by decide⟩ (UInt256.ofNat t.dest) hv.2.2.2.1 hfit
  · simpa [hv.2.2.2.2.1] using
      Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.decodeAt_op_index (t.srcIndex + 2) .JUMP
        hv.2.2.2.2.2.1 (by decide) trivial
  · simpa [hv.2.2.2.2.2.2.1] using
      Challenge.Sha256.Reference.Proofs.Bytecode.Artifact.isValidJumpDest_index t.destIndex
        hv.2.2.2.2.2.2.2

noncomputable def gasSteps_entryLink (calldata : ByteArray) (src dest : Nat)
    (hlink : (src, dest) ∈ entryLinks) :
    Challenge.EvmProof.GasSteps (atPC calldata src) (atPC calldata dest) := by
  rw [entryLinks] at hlink
  let t := Classical.choose (List.mem_map.mp hlink)
  have ht : t ∈ Artifact.entryTrampolines :=
    (Classical.choose_spec (List.mem_map.mp hlink)).1
  have hp : (t.src, t.dest) = (src, dest) :=
    (Classical.choose_spec (List.mem_map.mp hlink)).2
  have hsrc : t.src = src := congrArg Prod.fst hp
  have hdest : t.dest = dest := congrArg Prod.snd hp
  rw [← hsrc, ← hdest]
  exact gasSteps_entryTrampoline calldata t ht

/-- The complete compiler-generated entry chain lands at the SHA body. -/
def gasSteps_to_main (calldata : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode calldata 0)
      (atPC calldata mainPC) := by
  have l₁ := gasSteps_entryTrampoline calldata ⟨0x001b, 0x0044, 20, 48⟩
    (by simp [Artifact.entryTrampolines])
  have l₂ := gasSteps_entryTrampoline calldata ⟨0x0044, 0x006d, 48, 76⟩
    (by simp [Artifact.entryTrampolines])
  have l₃ := gasSteps_entryTrampoline calldata ⟨0x006d, 0x009e, 76, 108⟩
    (by simp [Artifact.entryTrampolines])
  have l₄ := gasSteps_entryTrampoline calldata ⟨0x009e, 0x00cf, 108, 140⟩
    (by simp [Artifact.entryTrampolines])
  have l₅ := gasSteps_entryTrampoline calldata ⟨0x00cf, 0x00e4, 140, 159⟩
    (by simp [Artifact.entryTrampolines])
  have l₆ := gasSteps_entryTrampoline calldata ⟨0x00e4, 0x00fc, 159, 181⟩
    (by simp [Artifact.entryTrampolines])
  have l₇ := gasSteps_entryTrampoline calldata ⟨0x00fc, 0x0112, 181, 198⟩
    (by simp [Artifact.entryTrampolines])
  have l₈ := gasSteps_entryTrampoline calldata ⟨0x0112, 0x0126, 198, 213⟩
    (by simp [Artifact.entryTrampolines])
  have l₉ := gasSteps_entryTrampoline calldata ⟨0x0126, 0x0139, 213, 227⟩
    (by simp [Artifact.entryTrampolines])
  have l₁₀ := gasSteps_entryTrampoline calldata ⟨0x0139, 0x014d, 227, 242⟩
    (by simp [Artifact.entryTrampolines])
  have l₁₁ := gasSteps_entryTrampoline calldata ⟨0x014d, 0x0160, 242, 256⟩
    (by simp [Artifact.entryTrampolines])
  have l₁₂ := gasSteps_entryTrampoline calldata ⟨0x0160, 0x01b9, 256, 322⟩
    (by simp [Artifact.entryTrampolines])
  have l₁₃ := gasSteps_entryTrampoline calldata ⟨0x01b9, 0x025f, 322, 432⟩
    (by simp [Artifact.entryTrampolines])
  have l₁₄ := gasSteps_entryTrampoline calldata ⟨0x025f, mainPC, 432, 658⟩
    (by simp [Artifact.entryTrampolines, mainPC])
  exact (gasSteps_to_firstTarget calldata).trans
    (l₁.trans
    (l₂.trans (l₃.trans (l₄.trans (l₅.trans (l₆.trans (l₇.trans
    (l₈.trans (l₉.trans (l₁₀.trans (l₁₁.trans (l₁₂.trans
    (l₁₃.trans l₁₄)))))))))))))

end Challenge.Sha256.Reference.Proofs.Bytecode.Reference
