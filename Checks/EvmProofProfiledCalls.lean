import Challenge.EvmProof.ModexpCallRealization
set_option warningAsError true
/-!
# Profile-preserving external-call checks
-/

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open YulEvmCompiler

example {external : ExternalCalls} {config : PrecompileConfig}
    (h : Challenge.EvmProof.ProfiledCallsRealized external config)
    {yop : Op} (hcall : IsCallOp yop) {o : Operation}
    (hop : opTable yop = some o) {args rets : List U256}
    {yst yst' : EvmState}
    (hsource : builtin external yop args yst (.ok rets yst')) :
    ∃ bnd : Nat, ∀ {code : ByteArray} {s : State} {σ : List UInt256},
      FrameOK code s → StateMatch yst s →
      Challenge.EvmProof.CallerProfile config s →
      s.decodedOp = some o → s.stack = args.map conv ++ σ →
      bnd ≤ s.gasAvailable →
      s.stack.length + o.pushArity ≤ 1024 + o.popArity →
      ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s' ∧
        Challenge.EvmProof.CallerProfile config s' ∧
        s'.pc = s.pc.succ ∧ s'.stack = rets.map conv ++ σ ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable :=
  h.call hcall hop hsource

/-- info: 'Challenge.EvmProof.ProfiledCallsRealized.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.ProfiledCallsRealized.call

example (config : PrecompileConfig)
    (henabled : Precompile.isPrecompileWithConfig config .Osaka
      Precompile.modexpAddress = true) :
    Challenge.EvmProof.ProfiledCallsRealized
      Challenge.EvmProof.successfulModexpCalls config :=
  Challenge.EvmProof.successfulModexpCalls_realized config henabled

/-- info: 'Challenge.EvmProof.runWithConfig_modexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.runWithConfig_modexp

/-- info: 'Challenge.EvmProof.successfulModexpCalls_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.successfulModexpCalls_realized
