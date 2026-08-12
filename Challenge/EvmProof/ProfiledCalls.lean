import Challenge.EvmProof.ModexpCalls
import YulEvmCompiler.LowerDefs
set_option warningAsError true
/-!
# Profile-preserving Yul call realization

`YulEvmCompiler.CallsRealized` is the right open-world boundary for ordinary
contract calls.  A proof that deliberately invokes a native precompile also
needs target-only depth and configuration facts.  This strengthened boundary
threads `CallerProfile` through a complete call-and-return trace while
otherwise retaining the compiler's endpoint contract verbatim.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open YulEvmCompiler

/-- Realization of source calls that preserves a fixed caller execution
profile at the restored target endpoint. -/
structure ProfiledCallsRealized (external : ExternalCalls)
    (config : PrecompileConfig) : Prop where
  call {yop : Op} (hcall : IsCallOp yop) {o : Operation}
      (hop : opTable yop = some o) {args rets : List U256}
      {yst yst' : EvmState}
      (hsource : builtin external yop args yst (.ok rets yst')) :
      ∃ bnd : Nat, ∀ {code : ByteArray} {s : State} {σ : List UInt256},
        FrameOK code s → StateMatch yst s → CallerProfile config s →
        s.decodedOp = some o → s.stack = args.map conv ++ σ →
        bnd ≤ s.gasAvailable →
        s.stack.length + o.pushArity ≤ 1024 + o.popArity →
        ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s' ∧
          CallerProfile config s' ∧
          s'.pc = s.pc.succ ∧ s'.stack = rets.map conv ++ σ ∧
          s.gasAvailable - bnd ≤ s'.gasAvailable

end Challenge.EvmProof
