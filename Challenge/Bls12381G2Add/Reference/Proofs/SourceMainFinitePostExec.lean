import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteUnequalExec

set_option warningAsError true

/-! # Frozen G2ADD common affine postlude -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainPostBody_shape : mainPostBody =
    [mainFiniteStmt2, mainFiniteStmt3, mainFiniteStmt4, mainFiniteStmt5,
      mainFiniteStmt6, mainFiniteStmt7, mainFiniteStmt8, mainFiniteStmt9] := by rfl

private theorem mainFiniteStmt2_shape : mainFiniteStmt2 = .exprStmt
    (.call "\x0016" [.lit (.number 2688), .lit (.number 2048),
      .lit (.number 2048)]) := by rfl
private theorem mainFiniteStmt3_shape : mainFiniteStmt3 = .exprStmt
    (.call "\x0015" [.lit (.number 2688), .lit (.number 2688),
      .lit (.number 0)]) := by rfl
private theorem mainFiniteStmt4_shape : mainFiniteStmt4 = .exprStmt
    (.call "\x0015" [.lit (.number 2688), .lit (.number 2688),
      .lit (.number 256)]) := by rfl
private theorem mainFiniteStmt5_shape : mainFiniteStmt5 = .exprStmt
    (.call "\x0015" [.lit (.number 2816), .lit (.number 0),
      .lit (.number 2688)]) := by rfl
private theorem mainFiniteStmt6_shape : mainFiniteStmt6 = .exprStmt
    (.call "\x0016" [.lit (.number 2944), .lit (.number 2048),
      .lit (.number 2816)]) := by rfl
private theorem mainFiniteStmt7_shape : mainFiniteStmt7 = .exprStmt
    (.call "\x0015" [.lit (.number 2944), .lit (.number 2944),
      .lit (.number 128)]) := by rfl
private theorem mainFiniteStmt8_shape : mainFiniteStmt8 = .exprStmt
    (.call "\x0024" [.lit (.number 2688), .lit (.number 2944)]) := by rfl
private theorem mainFiniteStmt9_shape : mainFiniteStmt9 = .exprStmt
    (.builtin .ret [.lit (.number 0), .lit (.number 256)]) := by rfl

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

private theorem eval_mainStorePoint (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns [] yst
      (.call "\x0024" [.lit (.number 2688), .lit (.number 2944)]) =
    .ok (.vals [] (storePointState yst 2688 2944)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns [] yst
      [.lit (.number 2688), .lit (.number 2944)] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
      [("x", (2688 : U256)), ("y", (2944 : U256))] yst
      [.var "x", .var "y"] := by rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x0024") hargs (by rfl)]
  exact eval_storePoint 2688 2944 yst

theorem step_mainPostBody (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns [] yst
      mainPostBody [] (mainPostReturnState yst) .halt := by
  rw [mainPostBody_shape, mainFiniteStmt2_shape, mainFiniteStmt3_shape,
    mainFiniteStmt4_shape, mainFiniteStmt5_shape, mainFiniteStmt6_shape,
    mainFiniteStmt7_shape, mainFiniteStmt8_shape, mainFiniteStmt9_shape]
  have hstore : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainPostState5 yst)
      (.call "\x0024" [.lit (.number 2688), .lit (.number 2944)])
      (.vals [] (mainPostStoredState yst)) :=
    sound_evalExpr (eval_mainStorePoint (mainPostState5 yst))
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns []
      (mainPostStoredState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 256)])
      (.halt (mainPostReturnState yst)) :=
    Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl
  exact Step.seqCons (Step.exprStmt (step_fp2MulLiteral [] _ 2688 2048 2048))
    (Step.seqCons (Step.exprStmt (step_fp2SubLiteral [] _ 2688 2688 0))
      (Step.seqCons (Step.exprStmt (step_fp2SubLiteral [] _ 2688 2688 256))
        (Step.seqCons (Step.exprStmt (step_fp2SubLiteral [] _ 2816 0 2688))
          (Step.seqCons (Step.exprStmt
            (step_fp2MulLiteral [] _ 2944 2048 2816))
            (Step.seqCons (Step.exprStmt
              (step_fp2SubLiteral [] _ 2944 2944 128))
              (Step.seqCons (Step.exprStmt hstore)
                (Step.seqStop (Step.exprStmtHalt hret) (by decide))))))))

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
