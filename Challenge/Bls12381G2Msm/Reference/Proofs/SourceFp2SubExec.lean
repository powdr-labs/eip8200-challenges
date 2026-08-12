import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2SubBody

set_option warningAsError true

/-! Frozen G2MSM `fp2Sub` execution endpoint. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_fp2Sub (out a b : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 72 fp2SubFuns
      [("out", out), ("a", a), ("b", b)] yst
      (.call "\x0015" [.var "out", .var "a", .var "b"]) =
    .ok (.vals [] (fp2SubFinalState yst out a b)) := by
  have hcall := Interp.evalExpr_call_normal
    (E := Challenge.EvmProof.modexpExec) (n := 71)
    (V := [("out", out), ("a", a), ("b", b)]) (st := yst)
    (args := [.var "out", .var "a", .var "b"])
    (argvals := [out, a, b]) (fn := "\x0015")
    (decl := fp2SubDecl) (cenv := fp2SubFuns)
    (Vend := fp2SubBodyResultEnv yst out a b)
    (st2 := fp2SubFinalState yst out a b)
    (by rfl) lookup_fp2Sub (by rfl) (exec_fp2SubBody yst out a b)
  change Interp.evalExpr Challenge.EvmProof.modexpExec 72 fp2SubFuns
      [("out", out), ("a", a), ("b", b)] yst
      (.call "\x0015" [.var "out", .var "a", .var "b"]) =
    .ok (.vals
      (List.map (fun r =>
        (VEnv.get (fp2SubBodyResultEnv yst out a b) r).getD
          Challenge.EvmProof.modexpExec.zero) fp2SubDecl.rets)
      (fp2SubFinalState yst out a b)) at hcall
  have hrets :
      List.map (fun r =>
        (VEnv.get (fp2SubBodyResultEnv yst out a b) r).getD
          Challenge.EvmProof.modexpExec.zero) fp2SubDecl.rets = [] := by
    rfl
  rw [hrets] at hcall
  exact hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
