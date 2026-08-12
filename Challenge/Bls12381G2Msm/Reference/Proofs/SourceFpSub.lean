import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpSubExec

set_option warningAsError true

/-! Complete frozen G2MSM `fpSub` evaluator endpoint. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpSubBody (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 63 fpSubFuns
      (fpSubInitialEnv ahi alo bhi blo) yst (.block fpSubBody) =
    .ok (fpSubFinalEnv ahi alo bhi blo, yst, .normal) := by
  have hseq : Interp.execStmts modexpExec 62 fpSubBodyFuns
      (fpSubInitialEnv ahi alo bhi blo) yst
      [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3] =
      .ok (fpSubBodyFinalEnv ahi alo bhi blo, yst, .normal) := by
    cases hcondition : BitVec.ult fpModulusHiValue
        (fpSubRawHighValue ahi alo bhi blo)
    · have h3 := Interp.execStmts_cons_normal
        (exec_fpSubStmt3_keep ahi alo bhi blo yst hcondition)
        (show Interp.execStmts modexpExec 58 fpSubBodyFuns
          (fpSubPreBranchEnv ahi alo bhi blo) yst [] =
          .ok (fpSubPreBranchEnv ahi alo bhi blo, yst, .normal) by rfl)
      have h2 := Interp.execStmts_cons_normal
        (exec_fpSubStmt2 ahi alo bhi blo yst) h3
      have h1 := Interp.execStmts_cons_normal
        (exec_fpSubStmt1 ahi alo bhi blo yst) h2
      have h0 := Interp.execStmts_cons_normal
        (exec_fpSubStmt0 ahi alo bhi blo yst) h1
      simpa [fpSubBodyFinalEnv, hcondition] using h0
    · have h3 := Interp.execStmts_cons_normal
        (exec_fpSubStmt3_repair ahi alo bhi blo yst hcondition)
        (show Interp.execStmts modexpExec 58 fpSubBodyFuns
          (fpSubRepairedEnv ahi alo bhi blo) yst [] =
          .ok (fpSubRepairedEnv ahi alo bhi blo, yst, .normal) by rfl)
      have h2 := Interp.execStmts_cons_normal
        (exec_fpSubStmt2 ahi alo bhi blo yst) h3
      have h1 := Interp.execStmts_cons_normal
        (exec_fpSubStmt1 ahi alo bhi blo yst) h2
      have h0 := Interp.execStmts_cons_normal
        (exec_fpSubStmt0 ahi alo bhi blo yst) h1
      simpa [fpSubBodyFinalEnv, hcondition] using h0
  rw [Interp.execStmt]
  rw [show fpSubBody = [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3] by rfl]
  rw [show hoist modexpExec.toDialect
    [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3] = [] by rfl]
  change (do
    let x ← Interp.execStmts modexpExec 62 fpSubBodyFuns
      (fpSubInitialEnv ahi alo bhi blo) yst
      [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3]
    .ok (restore (fpSubInitialEnv ahi alo bhi blo) x.1, x.2.1, x.2.2)) = _
  rw [hseq]
  rfl

theorem fpSubResult_eq_value (ahi alo bhi blo : U256) :
    fpSubResult ahi alo bhi blo = fpSubValue ahi alo bhi blo := by
  cases hcondition : BitVec.ult fpModulusHiValue
      (fpSubRawHighValue ahi alo bhi blo)
  · have hcondition' : BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue
          ahi alo bhi blo).1 = false := by
      simpa [fpSubRawHighValue, fpModulusHiValue,
        Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue]
        using hcondition
    unfold fpSubResult fpSubFinalEnv fpSubBodyFinalEnv
    simp [hcondition, restore, fpSubPreBranchEnv, fpSubRawEnv, fpSubLowEnv,
      fpSubInitialEnv, VEnv.setMany, VEnv.set]
    change (fpSubRawHighValue ahi alo bhi blo, fpSubRawLowValue alo blo) =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
        ahi alo bhi blo
    have hneeds :
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue
          (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue
            ahi alo bhi blo) = 0 := by
      unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue
      rw [hcondition']
      rfl
    unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
    rw [if_pos hneeds]
    rfl
  · have hcondition' : BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue
          ahi alo bhi blo).1 = true := by
      simpa [fpSubRawHighValue, fpModulusHiValue,
        Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue]
        using hcondition
    unfold fpSubResult fpSubFinalEnv fpSubBodyFinalEnv
    simp [hcondition, restore, fpSubRepairedEnv, fpSubPreBranchEnv,
      fpSubRawEnv, fpSubLowEnv, fpSubInitialEnv, VEnv.setMany, VEnv.set]
    change (fpSubRepairedHighValue ahi alo bhi blo,
      fpSubRepairedLowValue alo blo) =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
        ahi alo bhi blo
    have hneeds :
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue
          (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue
            ahi alo bhi blo) ≠ 0 := by
      unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue
      rw [hcondition']
      decide
    unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
    rw [if_neg hneeds]
    rfl

theorem eval_fpSub_raw (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 fpSubFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpSubResult ahi alo bhi blo).1,
      (fpSubResult ahi alo bhi blo).2] yst) := by
  have hcall := Interp.evalExpr_call_normal
    (E := modexpExec)
    (n := 63)
    (V := [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)])
    (st := yst)
    (args := [.var "ahi", .var "alo", .var "bhi", .var "blo"])
    (argvals := [ahi, alo, bhi, blo])
    (fn := "\x005")
    (decl := fpSubDecl)
    (cenv := fpSubFuns)
    (Vend := fpSubFinalEnv ahi alo bhi blo)
    (st2 := yst)
    (by rfl) lookup_fpSub (by rfl) (exec_fpSubBody ahi alo bhi blo yst)
  simpa [fpSubDecl, fpSubResult, Dialect.zero, litValue] using hcall

theorem eval_fpSub (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 fpSubFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpSubValue ahi alo bhi blo).1,
      (fpSubValue ahi alo bhi blo).2] yst) := by
  rw [eval_fpSub_raw, fpSubResult_eq_value]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
