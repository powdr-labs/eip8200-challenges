import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpAddExec

set_option warningAsError true

/-! Complete frozen G2MSM `fpAdd` evaluator endpoint. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpAddBody (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 63 fpAddFuns
      (fpAddInitialEnv ahi alo bhi blo) yst (.block fpAddBody) =
    .ok (fpAddFinalEnv ahi alo bhi blo, yst, .normal) := by
  have hseq : Interp.execStmts modexpExec 62 fpAddBodyFuns
      (fpAddInitialEnv ahi alo bhi blo) yst
      [fpAddStmt0, fpAddStmt1, fpAddStmt2] =
      .ok (fpAddFinalEnv ahi alo bhi blo, yst, .normal) := by
    by_cases hcondition : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
        (fpAddLowValue alo blo) = (0#256)
    · have h2 := Interp.execStmts_cons_normal
        (exec_fpAddStmt2_keep ahi alo bhi blo yst hcondition)
        (show Interp.execStmts modexpExec 59 fpAddBodyFuns
          (fpAddHighEnv ahi alo bhi blo) yst [] =
          .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) by rfl)
      have h1 := Interp.execStmts_cons_normal
        (exec_fpAddStmt1 ahi alo bhi blo yst) h2
      have h0 := Interp.execStmts_cons_normal
        (exec_fpAddStmt0 ahi alo bhi blo yst) h1
      simpa [fpAddFinalEnv, hcondition] using h0
    · have h2 := Interp.execStmts_cons_normal
        (exec_fpAddStmt2_correct ahi alo bhi blo yst hcondition)
        (show Interp.execStmts modexpExec 59 fpAddBodyFuns
          (fpAddCorrectEnv ahi alo bhi blo) yst [] =
          .ok (fpAddCorrectEnv ahi alo bhi blo, yst, .normal) by rfl)
      have h1 := Interp.execStmts_cons_normal
        (exec_fpAddStmt1 ahi alo bhi blo yst) h2
      have h0 := Interp.execStmts_cons_normal
        (exec_fpAddStmt0 ahi alo bhi blo yst) h1
      simpa [fpAddFinalEnv, hcondition] using h0
  rw [Interp.execStmt]
  rw [show fpAddBody = [fpAddStmt0, fpAddStmt1, fpAddStmt2] by rfl]
  rw [show hoist modexpExec.toDialect [fpAddStmt0, fpAddStmt1, fpAddStmt2] = [] by rfl]
  change (do
    let x ← Interp.execStmts modexpExec 62 fpAddBodyFuns
      (fpAddInitialEnv ahi alo bhi blo) yst [fpAddStmt0, fpAddStmt1, fpAddStmt2]
    .ok (restore (fpAddInitialEnv ahi alo bhi blo) x.1, x.2.1, x.2.2)) = _
  rw [hseq]
  simp only [Result.ok_bind]
  rw [restore_fpAddFinalEnv]

theorem fpAddResult_eq_value (ahi alo bhi blo : U256) :
    fpAddResult ahi alo bhi blo = fpAddValue ahi alo bhi blo := by
  by_cases hcondition : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) = (0#256)
  · unfold fpAddResult fpAddFinalEnv
    rw [if_pos hcondition]
    change (fpAddHighValue ahi alo bhi blo, fpAddLowValue alo blo) = _
    change _ = Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue
      ahi alo bhi blo
    have hcondition' :
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
          (ahi + bhi + b2w (BitVec.ult (alo + blo) alo)) (alo + blo) =
            (0#256) := by
      simpa [fpAddHighValue, fpAddLowValue] using hcondition
    simp [Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue,
      fpAddHighValue, fpAddLowValue, hcondition']
  · unfold fpAddResult fpAddFinalEnv
    rw [if_neg hcondition]
    change (fpAddCorrectHighValue ahi alo bhi blo,
      fpAddCorrectLowValue alo blo) = _
    change _ = Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue
      ahi alo bhi blo
    have hcondition' :
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
          (ahi + bhi + b2w (BitVec.ult (alo + blo) alo)) (alo + blo) ≠
            (0#256) := by
      simpa [fpAddHighValue, fpAddLowValue] using hcondition
    simp [fpAddCorrectHighValue, fpAddCorrectLowValue, fpAddHighValue,
      fpAddLowValue, fpModulusHiValue, fpModulusLoValue,
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue,
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusLoValue,
      hcondition']

theorem eval_fpAdd_raw (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 fpAddFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x004" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpAddResult ahi alo bhi blo).1,
      (fpAddResult ahi alo bhi blo).2] yst) := by
  have hcall := Interp.evalExpr_call_normal
    (E := modexpExec)
    (n := 63)
    (V := [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)])
    (st := yst)
    (args := [.var "ahi", .var "alo", .var "bhi", .var "blo"])
    (argvals := [ahi, alo, bhi, blo])
    (fn := "\x004")
    (decl := fpAddDecl)
    (cenv := fpAddFuns)
    (Vend := fpAddFinalEnv ahi alo bhi blo)
    (st2 := yst)
    (by rfl) lookup_fpAdd (by rfl) (exec_fpAddBody ahi alo bhi blo yst)
  simpa [fpAddDecl, fpAddResult, Dialect.zero, litValue] using hcall

theorem eval_fpAdd (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 fpAddFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x004" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpAddValue ahi alo bhi blo).1,
      (fpAddValue ahi alo bhi blo).2] yst) := by
  rw [eval_fpAdd_raw, fpAddResult_eq_value]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
