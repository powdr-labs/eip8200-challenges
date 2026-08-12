import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvStep

set_option warningAsError true

/-! Big-step call boundary for frozen G2MSM `fp2Inv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_fp2Inv (yst : EvmState) (out a : U256)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect fp2InvFuns
      [("out", out), ("a", a)] yst
      (.call "\x0017" [.var "out", .var "a"])
      (.vals [] (fp2InvFinalState yst out a)) := by
  have hargsEval :
      Interp.evalArgs Challenge.EvmProof.modexpExec 8 fp2InvFuns
        [("out", out), ("a", a)] yst [.var "out", .var "a"] =
      .ok (.vals [out, a] yst) := by rfl
  have hargs := (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 8).2.1
    _ _ _ _ _ hargsEval
  have hcall := Step.callOk hargs lookup_fp2Inv (by rfl)
    (step_fp2InvBody yst out a hhi) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect fp2InvFuns
    [("out", out), ("a", a)] yst
    (.call "\x0017" [.var "out", .var "a"])
    (.vals (fp2InvDecl.rets.map (fun r =>
      (VEnv.get (fp2InvBodyResultEnv yst out a) r).getD 0))
      (fp2InvFinalState yst out a)) at hcall
  simpa [fp2InvDecl] using hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
