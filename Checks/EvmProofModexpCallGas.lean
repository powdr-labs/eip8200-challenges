import Challenge.EvmProof.ModexpCallRealization
set_option warningAsError true
/-!
# MODEXP call gas helper checks
-/

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

example (available requested : Nat) (h : 65 * requested ≤ available) :
    Gas.forwardGas .Osaka available requested = requested :=
  Challenge.EvmProof.forwardGas_eq_arg_of_65_mul_le available requested h

/-- info: 'Challenge.EvmProof.staticcallCommitted_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.staticcallCommitted_le

/-- info: 'Challenge.EvmProof.forwardGas_eq_arg_of_65_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.forwardGas_eq_arg_of_65_mul_le

/-- info: 'Challenge.EvmProof.runModexp_success_gas_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.runModexp_success_gas_le
