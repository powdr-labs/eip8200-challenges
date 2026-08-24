import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleState

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainFiniteDoubleStmt2_shape : mainFiniteDoubleStmt2 =
    .assign ["\x00105", "\x00106"]
      (.call "\x004"
        [.var "\x00105", .var "\x00106",
          .var "\x00103", .var "\x00104"]) := by
  rfl

theorem exec_mainFiniteDoubleStmt2 (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 65 ([] :: mainFuns)
      (mainFiniteDoubleEnv2 yst) (mainFiniteDoubleState1 yst)
      mainFiniteDoubleStmt2 =
    .ok (mainFiniteDoubleEnv3 yst, mainFiniteDoubleState1 yst, .normal) := by
  let twice := mainFiniteDoubleTwiceWords yst
  let xSq := mainFiniteDoubleXSqWords yst
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 63 ([] :: mainFuns)
          (mainFiniteDoubleEnv2 yst) (mainFiniteDoubleState1 yst)
          [.var "\x00105", .var "\x00106",
            .var "\x00103", .var "\x00104"] =
        Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 63 mainFuns
          [("ahi", twice.1), ("alo", twice.2),
            ("bhi", xSq.1), ("blo", xSq.2)]
          (mainFiniteDoubleState1 yst)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs (show lookupFun ([] :: mainFuns) "\x004" =
      lookupFun mainFuns "\x004" by rfl)
  rw [mainFiniteDoubleStmt2_shape, Interp.execStmt, hcall]
  rw [show mainFuns = [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpAdd twice.1 twice.2 xSq.1 xSq.2]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
