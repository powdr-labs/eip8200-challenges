import Challenge.Bls12381G2Msm.Reference.Proofs.SourceInvalidLengthDefs
import Challenge.EvmProof.ModexpExec

set_option warningAsError true

/-! Interpreter prefix for the frozen G2MSM helper declarations. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

private theorem execStmts_function_prefix
    (E : ExecDialect) [DecidableEq E.toDialect.Value]
    (defs rest : List (Stmt E.toDialect.Op))
    (hdefs : defs.all isFunctionDefinition = true)
    (fuel : Nat) (hfuel : 0 < fuel) (funs V st) :
    Interp.execStmts E (fuel + defs.length) funs V st (defs ++ rest) =
      Interp.execStmts E fuel funs V st rest := by
  induction defs with
  | nil => simp
  | cons head tail ih =>
      have hparts : isFunctionDefinition head = true ∧
          tail.all isFunctionDefinition = true := by
        simpa using hdefs
      cases head <;> simp only [isFunctionDefinition, Bool.false_eq_true] at hparts
      all_goals try { exact False.elim hparts.1 }
      case funDef name params rets body =>
        have hpositive : 0 < fuel + tail.length := by omega
        obtain ⟨k, hk⟩ : ∃ k, fuel + tail.length = k + 1 :=
          ⟨fuel + tail.length - 1, by omega⟩
        rw [show fuel + (Stmt.funDef name params rets body :: tail).length =
          (k + 1) + 1 by simp; omega]
        change Interp.execStmts E (k + 1) funs V st
          (tail ++ rest) = Interp.execStmts E fuel funs V st rest
        rw [← hk]
        exact ih hparts.2

theorem exec_reference_function_prefix (funs V st) :
    Interp.execStmts modexpExec 255 funs V st referenceCompiledBlock =
      Interp.execStmts modexpExec 224 funs V st
        (sizeStmt :: invalidLengthStmt :: referenceCompiledBlock.drop 33) := by
  have hprefix := execStmts_function_prefix modexpExec
    (referenceCompiledBlock.take 31) (referenceCompiledBlock.drop 31)
    reference_function_prefix 224 (by omega) funs V st
  rw [reference_function_prefix_length] at hprefix
  norm_num at hprefix
  calc
    Interp.execStmts modexpExec 255 funs V st referenceCompiledBlock =
        Interp.execStmts modexpExec 255 funs V st
          (referenceCompiledBlock.take 31 ++ referenceCompiledBlock.drop 31) := by
      rw [List.take_append_drop]
    _ = Interp.execStmts modexpExec 224 funs V st
          (referenceCompiledBlock.drop 31) := hprefix
    _ = Interp.execStmts modexpExec 224 funs V st
          (sizeStmt :: invalidLengthStmt :: referenceCompiledBlock.drop 33) := by
      rw [reference_after_functions]

private theorem stepStmts_function_prefix
    (D : Dialect) [DecidableEq D.Value]
    (defs rest : List (Stmt D.Op))
    (hdefs : defs.all isFunctionDefinition = true)
    {funs V st V' st' outcome}
    (htail : ExecStmts D funs V st rest V' st' outcome) :
    ExecStmts D funs V st (defs ++ rest) V' st' outcome := by
  induction defs with
  | nil => simpa using htail
  | cons head tail ih =>
      have hparts : isFunctionDefinition head = true ∧
          tail.all isFunctionDefinition = true := by
        simpa using hdefs
      cases head <;> simp only [isFunctionDefinition, Bool.false_eq_true] at hparts
      all_goals try { exact False.elim hparts.1 }
      case funDef =>
        exact Step.seqCons Step.funDef (ih hparts.2)

/-- Relational form of the frozen helper-declaration prefix.  Downstream
proofs supply only the small main-program suffix derivation. -/
theorem step_reference_function_prefix {funs V st V' st' outcome}
    (htail : ExecStmts modexpExec.toDialect funs V st
      (sizeStmt :: invalidLengthStmt :: referenceCompiledBlock.drop 33)
      V' st' outcome) :
    ExecStmts modexpExec.toDialect funs V st referenceCompiledBlock
      V' st' outcome := by
  have htail' : ExecStmts modexpExec.toDialect funs V st
      (referenceCompiledBlock.drop 31) V' st' outcome := by
    rw [reference_after_functions]
    exact htail
  have hprefix := stepStmts_function_prefix modexpExec.toDialect
    (referenceCompiledBlock.take 31) (referenceCompiledBlock.drop 31)
    reference_function_prefix htail'
  simpa only [List.take_append_drop] using hprefix

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
