import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2SubDefs
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpSub

set_option warningAsError true

/-! Staged scalar subtraction at the larger fuels used by Fp2 helpers. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_fpSub_extra (extra : Nat) (ahi alo bhi blo : U256)
    (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec (extra + 64) fp2SubFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpSubValue ahi alo bhi blo).1,
      (fpSubValue ahi alo bhi blo).2] yst) := by
  have hstmt0 :
      Interp.execStmt Challenge.EvmProof.modexpExec (extra + 61) fpSubBodyFuns
        (fpSubInitialEnv ahi alo bhi blo) yst fpSubStmt0 =
      .ok (fpSubLowEnv ahi alo bhi blo, yst, .normal) := by
    rfl
  have hstmt1 :
      Interp.execStmt Challenge.EvmProof.modexpExec (extra + 60) fpSubBodyFuns
        (fpSubLowEnv ahi alo bhi blo) yst fpSubStmt1 =
      .ok (fpSubRawEnv ahi alo bhi blo, yst, .normal) := by
    rfl
  have hstmt2 :
      Interp.execStmt Challenge.EvmProof.modexpExec (extra + 59) fpSubBodyFuns
        (fpSubRawEnv ahi alo bhi blo) yst fpSubStmt2 =
      .ok (fpSubPreBranchEnv ahi alo bhi blo, yst, .normal) := by
    rfl
  have hcondition :
      Interp.evalExpr Challenge.EvmProof.modexpExec (extra + 57) fpSubBodyFuns
        (fpSubPreBranchEnv ahi alo bhi blo) yst
        (.builtin .gt [.var "\x0060", .var "\x0062"]) =
      .ok (.vals [b2w (BitVec.ult fpModulusHiValue
        (fpSubRawHighValue ahi alo bhi blo))] yst) := by
    rfl
  have hbody :
      Interp.execStmt Challenge.EvmProof.modexpExec (extra + 63) fpSubFuns
        (fpSubInitialEnv ahi alo bhi blo) yst (.block fpSubBody) =
      .ok (fpSubFinalEnv ahi alo bhi blo, yst, .normal) := by
    have hseq :
        Interp.execStmts Challenge.EvmProof.modexpExec (extra + 62)
          fpSubBodyFuns (fpSubInitialEnv ahi alo bhi blo) yst
          [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3] =
        .ok (fpSubBodyFinalEnv ahi alo bhi blo, yst, .normal) := by
      cases hc : BitVec.ult fpModulusHiValue
          (fpSubRawHighValue ahi alo bhi blo)
      · have hstmt3 :
            Interp.execStmt Challenge.EvmProof.modexpExec (extra + 58)
              fpSubBodyFuns (fpSubPreBranchEnv ahi alo bhi blo) yst
              fpSubStmt3 =
            .ok (fpSubPreBranchEnv ahi alo bhi blo, yst, .normal) := by
          unfold fpSubStmt3
          rw [Interp.execStmt, hcondition]
          simp [Dialect.zero, b2w, litValue, hc]
        have h3 := Interp.execStmts_cons_normal hstmt3
          (show Interp.execStmts Challenge.EvmProof.modexpExec (extra + 58)
            fpSubBodyFuns (fpSubPreBranchEnv ahi alo bhi blo) yst [] =
            .ok (fpSubPreBranchEnv ahi alo bhi blo, yst, .normal) by rfl)
        have h2 := Interp.execStmts_cons_normal hstmt2 h3
        have h1 := Interp.execStmts_cons_normal hstmt1 h2
        have h0 := Interp.execStmts_cons_normal hstmt0 h1
        simpa [fpSubBodyFinalEnv, hc] using h0
      · have hstmt3 :
            Interp.execStmt Challenge.EvmProof.modexpExec (extra + 58)
              fpSubBodyFuns (fpSubPreBranchEnv ahi alo bhi blo) yst
              fpSubStmt3 =
            .ok (fpSubRepairedEnv ahi alo bhi blo, yst, .normal) := by
          unfold fpSubStmt3
          rw [Interp.execStmt, hcondition]
          simp only [Result.ok_bind, Dialect.zero, b2w, hc, litValue]
          simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr,
            Interp.evalArgs, Challenge.EvmProof.modexpExec,
            Challenge.EvmProof.modexpBuiltinFn, stepOp, bin, litValue,
            VEnv.get, VEnv.setMany, VEnv.set, restore,
            fpSubPreBranchEnv, fpSubRawEnv, fpSubLowEnv, fpSubInitialEnv,
            fpSubRepairedEnv, fpSubRepairedHighValue, fpSubRepairedLowValue,
            fpModulusHiValue, fpModulusLoValue,
            Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
            Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusLoValue]
        have h3 := Interp.execStmts_cons_normal hstmt3
          (show Interp.execStmts Challenge.EvmProof.modexpExec (extra + 58)
            fpSubBodyFuns (fpSubRepairedEnv ahi alo bhi blo) yst [] =
            .ok (fpSubRepairedEnv ahi alo bhi blo, yst, .normal) by rfl)
        have h2 := Interp.execStmts_cons_normal hstmt2 h3
        have h1 := Interp.execStmts_cons_normal hstmt1 h2
        have h0 := Interp.execStmts_cons_normal hstmt0 h1
        simpa [fpSubBodyFinalEnv, hc] using h0
    rw [Interp.execStmt]
    rw [show fpSubBody = [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3]
      by rfl]
    rw [show hoist Challenge.EvmProof.modexpExec.toDialect
      [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3] = [] by rfl]
    change (do
      let x ← Interp.execStmts Challenge.EvmProof.modexpExec (extra + 62)
        fpSubBodyFuns (fpSubInitialEnv ahi alo bhi blo) yst
        [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3]
      .ok (restore (fpSubInitialEnv ahi alo bhi blo) x.1, x.2.1, x.2.2)) = _
    rw [hseq]
    rfl
  have hcall := Interp.evalExpr_call_normal
    (E := Challenge.EvmProof.modexpExec)
    (n := extra + 63)
    (V := [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)])
    (st := yst)
    (args := [.var "ahi", .var "alo", .var "bhi", .var "blo"])
    (argvals := [ahi, alo, bhi, blo])
    (fn := "\x005")
    (decl := fpSubDecl)
    (cenv := fpSubFuns)
    (Vend := fpSubFinalEnv ahi alo bhi blo)
    (st2 := yst)
    (by rfl) lookup_fpSub (by rfl) hbody
  have hraw :
      Interp.evalExpr Challenge.EvmProof.modexpExec (extra + 64) fpSubFuns
        [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
        (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
      .ok (.vals [(fpSubResult ahi alo bhi blo).1,
        (fpSubResult ahi alo bhi blo).2] yst) := by
    simpa [fpSubDecl, fpSubResult, Dialect.zero, litValue] using hcall
  rw [show fp2SubFuns = fpSubFuns by rfl, hraw, fpSubResult_eq_value]

theorem eval_fpSub68 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2SubFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpSubValue ahi alo bhi blo).1,
      (fpSubValue ahi alo bhi blo).2] yst) :=
  eval_fpSub_extra 4 ahi alo bhi blo yst

theorem eval_fpSub65 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 fp2SubFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpSubValue ahi alo bhi blo).1,
      (fpSubValue ahi alo bhi blo).2] yst) :=
  eval_fpSub_extra 1 ahi alo bhi blo yst

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
