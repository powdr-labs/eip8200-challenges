import Challenge.EvmProof.ModexpCalls
set_option warningAsError true
/-!
# Profiled MODEXP-call checks

The compiler's generic external-call contract deliberately abstracts away
target-only execution data.  Successful precompile realization needs the two
facts below explicitly: the call-depth guard and the configured precompile
set.  These examples keep that strengthened boundary public and reusable.
-/

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM

example {config : PrecompileConfig} {s : State}
    (h : Challenge.EvmProof.CallerProfile config s) :
    s.executionEnv.depth < 1024 := h.depth

example {config : PrecompileConfig} {s : State}
    (h : Challenge.EvmProof.CallerProfile config s) :
    s.executionEnv.precompileConfig = config := h.precompileConfig

example {req : CallRequest} {yst : EvmState} {response : CallResponse}
    (h : Challenge.EvmProof.successfulModexpCalls.Call req yst response) :
    req.kind = .staticcall := h.kind

example {req : CallRequest} {yst : EvmState} {response : CallResponse}
    (h : Challenge.EvmProof.successfulModexpCalls.Call req yst response) :
    req.target = BitVec.ofNat 256 5 := h.target

example {req : CallRequest} {yst : EvmState} {response : CallResponse}
    (h : Challenge.EvmProof.successfulModexpCalls.Call req yst response) :
    response.success = true := h.success

/-- info: 'Challenge.EvmProof.SuccessfulModexpCall.kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.SuccessfulModexpCall.kind

/-- info: 'Challenge.EvmProof.SuccessfulModexpCall.target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.SuccessfulModexpCall.target

/-- info: 'Challenge.EvmProof.SuccessfulModexpCall.value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.SuccessfulModexpCall.value

/-- info: 'Challenge.EvmProof.SuccessfulModexpCall.success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.SuccessfulModexpCall.success
