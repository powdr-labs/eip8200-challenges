import Challenge.EvmProof.ModexpExec

set_option warningAsError true

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

example {op args st result}
    (h : Challenge.EvmProof.modexpBuiltinFn op args st = some result) :
    (evmWithExternal Challenge.EvmProof.successfulModexpCalls
      ExternalCreates.none).Builtin op args st result :=
  Challenge.EvmProof.modexpBuiltinFn_sound h

example {fuel program st0 V' st' outcome}
    (h : Interp.run Challenge.EvmProof.modexpExec fuel program st0 =
      .ok (V', st', outcome)) :
    Run Challenge.EvmProof.modexpExec.toDialect program st0 V' st' outcome :=
  Challenge.EvmProof.modexpExec_run_sound h

/-- info: 'Challenge.EvmProof.modexpBuiltinFn_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.modexpBuiltinFn_sound

/-- info: 'Challenge.EvmProof.modexpExec_run_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.modexpExec_run_sound
