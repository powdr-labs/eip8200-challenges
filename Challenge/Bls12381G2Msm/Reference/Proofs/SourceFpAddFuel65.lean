import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AddStart

set_option warningAsError true

/-! The frozen scalar addition endpoint at the second Fp2 call's fuel. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_fpAdd65 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 fp2AddFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x004" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpAddValue ahi alo bhi blo).1,
      (fpAddValue ahi alo bhi blo).2] yst) := by
  have hstmt0 :
      Interp.execStmt Challenge.EvmProof.modexpExec 62 fpAddBodyFuns
        (fpAddInitialEnv ahi alo bhi blo) yst fpAddStmt0 =
      .ok (fpAddLowEnv ahi alo bhi blo, yst, .normal) := by
    rfl
  have hstmt1 :
      Interp.execStmt Challenge.EvmProof.modexpExec 61 fpAddBodyFuns
        (fpAddLowEnv ahi alo bhi blo) yst fpAddStmt1 =
      .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) := by
    rfl
  have hcondition :
      Interp.evalExpr Challenge.EvmProof.modexpExec 59 fpAddBodyFuns
        (fpAddHighEnv ahi alo bhi blo) yst
        (.call "\x000" [.var "\x0051", .var "\x0052"]) =
      .ok (.vals [fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
        (fpAddLowValue alo blo)] yst) := by
    rw [Interp.evalExpr]
    rfl
  have hbody :
      Interp.execStmt Challenge.EvmProof.modexpExec 64 fpAddFuns
        (fpAddInitialEnv ahi alo bhi blo) yst (.block fpAddBody) =
      .ok (fpAddFinalEnv ahi alo bhi blo, yst, .normal) := by
    have hseq : Interp.execStmts Challenge.EvmProof.modexpExec 63 fpAddBodyFuns
        (fpAddInitialEnv ahi alo bhi blo) yst
        [fpAddStmt0, fpAddStmt1, fpAddStmt2] =
        .ok (fpAddFinalEnv ahi alo bhi blo, yst, .normal) := by
      by_cases hc : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
          (fpAddLowValue alo blo) = (0#256)
      · have hstmt2 :
            Interp.execStmt Challenge.EvmProof.modexpExec 60 fpAddBodyFuns
              (fpAddHighEnv ahi alo bhi blo) yst fpAddStmt2 =
            .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) := by
          unfold fpAddStmt2
          rw [Interp.execStmt, hcondition]
          simp [Dialect.zero, litValue, hc]
        have h2 := Interp.execStmts_cons_normal hstmt2
          (show Interp.execStmts Challenge.EvmProof.modexpExec 60 fpAddBodyFuns
            (fpAddHighEnv ahi alo bhi blo) yst [] =
            .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) by rfl)
        have h1 := Interp.execStmts_cons_normal hstmt1 h2
        have h0 := Interp.execStmts_cons_normal hstmt0 h1
        simpa [fpAddFinalEnv, hc] using h0
      · have hstmt2 :
            Interp.execStmt Challenge.EvmProof.modexpExec 60 fpAddBodyFuns
              (fpAddHighEnv ahi alo bhi blo) yst fpAddStmt2 =
            .ok (fpAddCorrectEnv ahi alo bhi blo, yst, .normal) := by
          unfold fpAddStmt2
          rw [Interp.execStmt, hcondition]
          simp only [Result.ok_bind, Dialect.zero, litValue]
          rw [if_neg hc]
          simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr,
            Interp.evalArgs, Challenge.EvmProof.modexpExec,
            Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, litValue,
            VEnv.get, VEnv.setMany, VEnv.set, restore,
            fpAddHighEnv, fpAddLowEnv, fpAddInitialEnv, fpAddCorrectEnv,
            fpAddCorrectHighValue, fpAddCorrectLowValue,
            fpModulusHiValue, fpModulusLoValue,
            Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
            Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusLoValue]
        have h2 := Interp.execStmts_cons_normal hstmt2
          (show Interp.execStmts Challenge.EvmProof.modexpExec 60 fpAddBodyFuns
            (fpAddCorrectEnv ahi alo bhi blo) yst [] =
            .ok (fpAddCorrectEnv ahi alo bhi blo, yst, .normal) by rfl)
        have h1 := Interp.execStmts_cons_normal hstmt1 h2
        have h0 := Interp.execStmts_cons_normal hstmt0 h1
        simpa [fpAddFinalEnv, hc] using h0
    rw [Interp.execStmt]
    rw [show fpAddBody = [fpAddStmt0, fpAddStmt1, fpAddStmt2] by rfl]
    rw [show hoist Challenge.EvmProof.modexpExec.toDialect
      [fpAddStmt0, fpAddStmt1, fpAddStmt2] = [] by rfl]
    change (do
      let x ← Interp.execStmts Challenge.EvmProof.modexpExec 63 fpAddBodyFuns
        (fpAddInitialEnv ahi alo bhi blo) yst
        [fpAddStmt0, fpAddStmt1, fpAddStmt2]
      .ok (restore (fpAddInitialEnv ahi alo bhi blo) x.1, x.2.1, x.2.2)) = _
    rw [hseq]
    simp only [Result.ok_bind]
    rw [restore_fpAddFinalEnv]
  have hcall := Interp.evalExpr_call_normal
    (E := Challenge.EvmProof.modexpExec)
    (n := 64)
    (V := [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)])
    (st := yst)
    (args := [.var "ahi", .var "alo", .var "bhi", .var "blo"])
    (argvals := [ahi, alo, bhi, blo])
    (fn := "\x004")
    (decl := fpAddDecl)
    (cenv := fpAddFuns)
    (Vend := fpAddFinalEnv ahi alo bhi blo)
    (st2 := yst)
    (by rfl) lookup_fpAdd (by rfl) hbody
  have hraw : Interp.evalExpr Challenge.EvmProof.modexpExec 65 fpAddFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x004" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpAddResult ahi alo bhi blo).1,
      (fpAddResult ahi alo bhi blo).2] yst) := by
    simpa [fpAddDecl, fpAddResult, Dialect.zero, litValue] using hcall
  rw [show fp2AddFuns = fpAddFuns by rfl, hraw, fpAddResult_eq_value]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
