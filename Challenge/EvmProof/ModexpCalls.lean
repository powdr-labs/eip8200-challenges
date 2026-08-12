import EvmSemantics.EVM.Step
import YulSemantics.Dialect.EVMExec
set_option warningAsError true
/-!
# Successful MODEXP calls at the Yul/EVM boundary

The verified Yul compiler's generic `CallsRealized` interface relates source
and target states, but intentionally does not constrain target call depth or
the target precompile configuration.  A successful native precompile call
cannot be derived from that interface alone: the otherwise matching target
may be at the depth limit or may have disabled address `0x05`.

This module records those target-only premises explicitly and defines the
narrow source relation used by proof-friendly programs that call MODEXP.  It
is generic EVM proof infrastructure rather than BLS-specific arithmetic.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM

/-- Target execution facts required to realize a successful precompile call.

The profile is deliberately separate from the compiler's extensional
`StateMatch`: neither field is observable in the gas-free source semantics.
-/
structure CallerProfile (config : PrecompileConfig) (s : State) : Prop where
  depth : s.executionEnv.depth < 1024
  precompileConfig : s.executionEnv.precompileConfig = config

/-- Source-side description of one successful static call to MODEXP.

The response exposes exactly the precompile output and does not mutate the
source world.  Call-local memory placement is still performed by
`YulSemantics.EVM.finishCall`, outside this relation.
-/
def SuccessfulModexpCall (req : CallRequest) (yst : EvmState)
    (response : CallResponse) : Prop :=
  req.kind = .staticcall ∧
  req.target = BitVec.ofNat 256 5 ∧
  req.value = 0 ∧
  ∃ output gasUsed,
    Precompile.runModexp .Osaka ⟨req.input.toArray⟩ req.gas.toNat =
      .success output gasUsed ∧
    response.success = true ∧
    response.returndata = output.toList ∧
    response.world = CallWorld.ofState yst

namespace SuccessfulModexpCall

theorem kind {req : CallRequest} {yst : EvmState} {response : CallResponse}
    (h : SuccessfulModexpCall req yst response) : req.kind = .staticcall :=
  h.1

theorem target {req : CallRequest} {yst : EvmState} {response : CallResponse}
    (h : SuccessfulModexpCall req yst response) :
    req.target = BitVec.ofNat 256 5 :=
  h.2.1

theorem value {req : CallRequest} {yst : EvmState} {response : CallResponse}
    (h : SuccessfulModexpCall req yst response) : req.value = 0 :=
  h.2.2.1

theorem success {req : CallRequest} {yst : EvmState} {response : CallResponse}
    (h : SuccessfulModexpCall req yst response) : response.success = true := by
  obtain ⟨_, _, _, output, gasUsed, _, hsuccess, _⟩ := h
  exact hsuccess

end SuccessfulModexpCall

/-- External-call relation containing exactly successful Osaka MODEXP calls. -/
def successfulModexpCalls : ExternalCalls where
  Call := SuccessfulModexpCall

end Challenge.EvmProof
