import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvBody

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem eval_fpInv_args (hi lo : U256) (yst : EvmState) :
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpInvFuns
      [("hi", hi), ("lo", lo)] yst [.var "hi", .var "lo"] =
    .ok (.vals [hi, lo] yst) := by
  rfl

/-- The frozen helper executes the complete source `fpInv` schedule,
including its successful literal-gas MODEXP call and output loads. -/
theorem eval_fpInv (hi lo : U256) (yst : EvmState)
    (hhi : hi.toNat < 2 ^ 128) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x0010" [.var "hi", .var "lo"]) =
    .ok (.vals [(fpInvResult yst hi lo).1, (fpInvResult yst hi lo).2]
      (fpInvFinalState yst hi lo)) := by
  have h := Interp.evalExpr_call_normal
    (eval_fpInv_args hi lo yst) lookup_fpInv (by rfl)
    (exec_fpInvBody hi lo yst hhi)
  change Interp.evalExpr Challenge.EvmProof.modexpExec 68 fpInvFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x0010" [.var "hi", .var "lo"]) =
    .ok (.vals
      [(VEnv.get (fpInvBodyResultEnv yst hi lo) "\x0079").getD 0,
        (VEnv.get (fpInvBodyResultEnv yst hi lo) "\x0080").getD 0]
      (fpInvFinalState yst hi lo)) at h
  rw [fpInvBodyResultEnv_hi, fpInvBodyResultEnv_lo] at h
  exact h

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
