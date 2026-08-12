import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulStep

set_option warningAsError true
/-! # Big-step call boundary for frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

theorem step_fp2Mul (yst : EvmState) (out a b : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect fp2MulFuns
      [("out", out), ("a", a), ("b", b)] yst
      (.call "\x0016" [.var "out", .var "a", .var "b"])
      (.vals [] (fp2MulFinalState yst out a b)) := by
  have hargsEval :
      Interp.evalArgs Challenge.EvmProof.modexpExec 8 fp2MulFuns
        [("out", out), ("a", a), ("b", b)] yst
        [.var "out", .var "a", .var "b"] =
      .ok (.vals [out, a, b] yst) := by rfl
  have hargs := (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 8).2.1
    _ _ _ _ _ hargsEval
  have hcall := Step.callOk hargs lookup_fp2Mul (by rfl)
    (step_fp2MulBody yst out a b) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect fp2MulFuns
    [("out", out), ("a", a), ("b", b)] yst
    (.call "\x0016" [.var "out", .var "a", .var "b"])
    (.vals (fp2MulDecl.rets.map (fun r =>
      (VEnv.get (fp2MulBodyResultEnv yst out a b) r).getD 0))
      (fp2MulFinalState yst out a b)) at hcall
  simpa [fp2MulDecl] using hcall

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
