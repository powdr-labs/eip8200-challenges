import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMontSecond
import Challenge.YulProof.Interpreter

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.YulProof.Interpreter

private abbrev E := Challenge.YulProof.ClosedEvm.exec

@[irreducible] def correctionEnv0 (xLo xHi yLo yHi : U256) : VEnv E.toDialect :=
  montMul2OutputEnv (montMul2InitialEnv xLo xHi yLo yHi)
    (montAccumulated xLo xHi yLo yHi) (montSecond xLo xHi yLo yHi)

theorem montMul2Stmt9_shape : montMul2Stmt9 =
    .cond (.call "\x000" [.var "\x00171", .var "\x00170"])
      [.letDecl ["\x00209"] (some (.lit (.number 34565483545414906068789196026815425751))),
       .letDecl ["\x00210"] (some (.lit (.number
        45442060874369865957053122457065728162598490762543039060009208264153100167851))),
       .letDecl ["\x00211"] (some (.builtin .sub [.var "\x00170", .var "\x00210"])),
       .assign ["\x00171"] (.builtin .sub
        [.builtin .sub [.var "\x00171", .var "\x00209"],
         .builtin .gt [.var "\x00210", .var "\x00170"]]),
       .assign ["\x00170"] (.var "\x00211")] := by
  rfl

set_option maxRecDepth 4096 in
theorem eval_montMul2CorrectionCondition (xLo xHi yLo yHi : U256)
    (yst : EvmState) :
    EvalExpr Challenge.YulProof.ClosedEvm.dialect montMul2BodyFuns
      (correctionEnv0 xLo xHi yLo yHi) yst
      (.call "\x000" [.var "\x00171", .var "\x00170"])
      (.vals [fpGeModulusValue (montSecond xLo xHi yLo yHi).t1
        (montSecond xLo xHi yLo yHi).t0] yst) := by
  apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 64)
  simp only [correctionEnv0]
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
    (E := E) (funs' := fpInvFuns)
    (V' := [("hi", (montSecond xLo xHi yLo yHi).t1),
      ("lo", (montSecond xLo xHi yLo yHi).t0)])
    (args' := [.var "hi", .var "lo"])
    (hargs := by rfl) (hlookup := lookup_fpGe_montMul2Body)]
  exact eval_fpGeModulus (montSecond xLo xHi yLo yHi).t1
    (montSecond xLo xHi yLo yHi).t0 yst

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
