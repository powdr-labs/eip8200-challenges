import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AddBody

set_option warningAsError true

/-! Frozen G2MSM `fp2Add` execution endpoint. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_fp2Add (out a b : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 72 fp2AddFuns
      [("out", out), ("a", a), ("b", b)] yst
      (.call "\x0014" [.var "out", .var "a", .var "b"]) =
    .ok (.vals [] (fp2AddFinalState yst out a b)) := by
  have hcall := Interp.evalExpr_call_normal
    (E := Challenge.EvmProof.modexpExec)
    (n := 71)
    (V := [("out", out), ("a", a), ("b", b)])
    (st := yst)
    (args := [.var "out", .var "a", .var "b"])
    (argvals := [out, a, b])
    (fn := "\x0014")
    (decl := fp2AddDecl)
    (cenv := fp2AddFuns)
    (Vend := fp2AddBodyResultEnv yst out a b)
    (st2 := fp2AddFinalState yst out a b)
    (by rfl) lookup_fp2Add (by rfl) (exec_fp2AddBody yst out a b)
  change Interp.evalExpr Challenge.EvmProof.modexpExec 72 fp2AddFuns
      [("out", out), ("a", a), ("b", b)] yst
      (.call "\x0014" [.var "out", .var "a", .var "b"]) =
    .ok (.vals
      (List.map (fun r =>
        (VEnv.get (fp2AddBodyResultEnv yst out a b) r).getD
          Challenge.EvmProof.modexpExec.zero) fp2AddDecl.rets)
      (fp2AddFinalState yst out a b)) at hcall
  have hrets :
      List.map (fun r =>
        (VEnv.get (fp2AddBodyResultEnv yst out a b) r).getD
          Challenge.EvmProof.modexpExec.zero) fp2AddDecl.rets = [] := by
    rfl
  rw [hrets] at hcall
  exact hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
