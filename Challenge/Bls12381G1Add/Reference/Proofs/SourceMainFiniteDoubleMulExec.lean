import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleInvExec

set_option warningAsError true

/-! # Interpreter execution of the final doubling-slope multiplication -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainFiniteDoubleStmt5_shape : mainFiniteDoubleStmt5 =
    .assign ["\x00101", "\x00102"]
      (.call "\x009"
        [.var "\x00105", .var "\x00106",
          .var "\x00109", .var "\x00110"]) := by
  rfl

/-- The final source multiplication writes the exact stable lambda words. -/
theorem exec_mainFiniteDoubleStmt5 (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 69 ([] :: mainFuns)
      (mainFiniteDoubleEnv5 yst) (mainFiniteDoubleState2 yst)
      mainFiniteDoubleStmt5 =
    .ok (mainFiniteDoubleEnv6 yst, mainFiniteDoubleFinalState yst,
      .normal) := by
  let num := mainFiniteDoubleNumeratorWords yst
  let denInv := mainFiniteDoubleDenInvWords yst
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 ([] :: mainFuns)
          (mainFiniteDoubleEnv5 yst) (mainFiniteDoubleState2 yst)
          [.var "\x00105", .var "\x00106",
            .var "\x00109", .var "\x00110"] =
        Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 mainFuns
          [("ahi", num.1), ("alo", num.2),
            ("bhi", denInv.1), ("blo", denInv.2)]
          (mainFiniteDoubleState2 yst)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs (show lookupFun ([] :: mainFuns) "\x009" =
      lookupFun mainFuns "\x009" by rfl)
  rw [mainFiniteDoubleStmt5_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul num.1 num.2 denInv.1 denInv.2
    (mainFiniteDoubleState2 yst)]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
