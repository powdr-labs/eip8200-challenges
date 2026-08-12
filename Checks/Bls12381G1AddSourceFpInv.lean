import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMemory

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (hi lo : U256) (yst : EvmState)
    (hhi : hi.toNat < 2 ^ 128) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x0010" [.var "hi", .var "lo"]) =
    .ok (.vals [(fpInvResult yst hi lo).1, (fpInvResult yst hi lo).2]
      (fpInvFinalState yst hi lo)) :=
  eval_fpInv hi lo yst hhi

example (hi lo : U256) (yst : EvmState)
    (hhi : hi.toNat < 2 ^ 128) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvOutputLimbs yst hi lo) :=
  canonical_fpInvOutput yst hi lo hhi

example (hi lo : U256) (yst : EvmState)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvInputLimbs hi lo)) :
    Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (fpInvOutputLimbs yst hi lo)) =
      (Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (fpInvInputLimbs hi lo)))⁻¹ :=
  fpInvOutput_toLawful yst hi lo ha

example (hi lo : U256) (yst : EvmState)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvInputLimbs hi lo)) :
    fpInvOutputLimbs yst hi lo =
      Challenge.Bls12381.ProofSupport.Fp.invCanonical
        (fpInvInputLimbs hi lo) :=
  fpInvOutput_eq_invCanonical yst hi lo ha

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpInvStores' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpInvStores

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpInvCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fpInvCall

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpInvOutput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpInvOutput

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpInvBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fpInvBody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvBodyResultEnv_hi' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvBodyResultEnv_hi

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvBodyResultEnv_lo' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvBodyResultEnv_lo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpInv

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutput_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvOutput_value

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_fpInvOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonical_fpInvOutput

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutput_toLawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvOutput_toLawful

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutput_eq_invCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvOutput_eq_invCanonical

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState_loadWord_before_scratch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpInvFinalState_loadWord_before_scratch

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
