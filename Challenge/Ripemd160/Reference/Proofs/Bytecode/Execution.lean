import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Entry of the frozen RIPEMD-160 reference bytecode

The optimized artifact emits no entry trampolines.  The old layout began
`PUSH2 0x1b; JUMP` and walked fourteen `JUMPDEST; PUSH2 next; JUMP` links to
reach the body at `0x3ef`; the new one places the initialization block at the
program entry and starts executing it at byte 0.

So the whole trampoline chain — `path_start`, `path_1b` … `path_3ee` and their
`gasSteps_*` links — is gone, together with its 156 gas.  `mainStart` is the
initial state itself, and `gasSteps_entry` is a cast of reflexivity.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

/-! The two word-arithmetic normalizers below are simp lemmas the modules above
this one rely on to fold a `pc` advance into a single literal.  They outlived the
trampoline chain that first needed them. -/

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

/-- Gas-erased reference state at a concrete program counter.  `GasSteps`
supplies the actual budget without duplicating otherwise identical states. -/
def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat pc }

/-- The body starts at byte 0: the first instruction is the first packed
lookup-table `PUSH31`, not a jump into a trampoline. -/
def mainStart (input : ByteArray) : State := atPC input 0

/-- `atPC` at the entry is the initial state itself. -/
@[simp] theorem atPC_zero (input : ByteArray) :
    atPC input 0 = initialState referenceBytecode input 0 := by
  rfl

/-- With no trampoline chain to walk, reaching the body is immediate. -/
def gasSteps_entry (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (mainStart input) :=
  Challenge.EvmProof.GasSteps.cast
    (Challenge.EvmProof.GasSteps.refl (initialState referenceBytecode input 0))
    rfl (by rw [show mainStart input = atPC input 0 from rfl, atPC_zero])

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution
