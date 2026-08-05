import Challenge.Sha256.Reference.Proofs.Bytecode
import Challenge.Sha256.Reference.Proofs.Bytecode.Artifact
import Challenge.Sha256.ProofSupport.InitialState
import EvmSemantics.EVM.StepDeterminism
set_option warningAsError true
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

/-- The optimized artifact emits no entry trampolines: the initialization block
sits at the program entry, so the body starts at byte 0. -/
def mainPC : Nat := 0

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

/-- `atPC` at the entry is the initial state itself, since the artifact starts
executing its first instruction at byte 0. -/
@[simp] theorem atPC_zero (calldata : ByteArray) :
    atPC calldata 0 = initialState referenceBytecode calldata 0 := by
  rfl

/-- With no trampoline chain to walk, reaching the body is immediate. -/
def gasSteps_to_main (calldata : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode calldata 0)
      (atPC calldata mainPC) :=
  Challenge.EvmProof.GasSteps.cast
    (Challenge.EvmProof.GasSteps.refl (initialState referenceBytecode calldata 0))
    rfl (by rw [show mainPC = 0 from rfl, atPC_zero])

end Challenge.Sha256.Reference.Proofs.Bytecode.Reference
