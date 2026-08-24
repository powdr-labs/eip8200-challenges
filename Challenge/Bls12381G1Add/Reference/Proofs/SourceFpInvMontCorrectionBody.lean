import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMontCondition

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.YulProof.Interpreter

private abbrev E := Challenge.YulProof.ClosedEvm.exec

private abbrev pHi : U256 :=
  BitVec.ofNat 256 34565483545414906068789196026815425751
private abbrev pLo : U256 := BitVec.ofNat 256
  45442060874369865957053122457065728162598490762543039060009208264153100167851

@[irreducible] def correctionEnv1 (xLo xHi yLo yHi : U256) : VEnv E.toDialect :=
  [("\x00209", pHi)] ++ correctionEnv0 xLo xHi yLo yHi

@[irreducible] def correctionEnv2 (xLo xHi yLo yHi : U256) : VEnv E.toDialect :=
  [("\x00210", pLo)] ++ correctionEnv1 xLo xHi yLo yHi

@[irreducible] def correctionEnv3 (xLo xHi yLo yHi : U256) : VEnv E.toDialect :=
  [("\x00211", (montSecond xLo xHi yLo yHi).t0 - pLo)] ++
    correctionEnv2 xLo xHi yLo yHi

@[irreducible] def correctionEnv4 (xLo xHi yLo yHi : U256) : VEnv E.toDialect :=
  VEnv.setMany (correctionEnv3 xLo xHi yLo yHi) ["\x00171"]
    [(montSecond xLo xHi yLo yHi).t1 - pHi -
      b2w (BitVec.ult (montSecond xLo xHi yLo yHi).t0 pLo)]

@[irreducible] def correctionEnv5 (xLo xHi yLo yHi : U256) : VEnv E.toDialect :=
  VEnv.setMany (correctionEnv4 xLo xHi yLo yHi) ["\x00170"]
    [(montSecond xLo xHi yLo yHi).t0 - pLo]

private theorem correctionStmt0 (xLo xHi yLo yHi : U256) (yst : EvmState) :
    Interp.execStmt E 8 ([] :: montMul2BodyFuns) (correctionEnv0 xLo xHi yLo yHi) yst
      (.letDecl ["\x00209"] (some (.lit (.number
        34565483545414906068789196026815425751)))) =
    .ok (correctionEnv1 xLo xHi yLo yHi, yst, .normal) := by
  simp only [correctionEnv1, correctionEnv0]
  rfl

private theorem correctionStmt1 (xLo xHi yLo yHi : U256) (yst : EvmState) :
    Interp.execStmt E 8 ([] :: montMul2BodyFuns) (correctionEnv1 xLo xHi yLo yHi) yst
      (.letDecl ["\x00210"] (some (.lit (.number
        45442060874369865957053122457065728162598490762543039060009208264153100167851)))) =
    .ok (correctionEnv2 xLo xHi yLo yHi, yst, .normal) := by
  simp only [correctionEnv2, correctionEnv1]
  rfl

private theorem correctionStmt2 (xLo xHi yLo yHi : U256) (yst : EvmState) :
    Interp.execStmt E 8 ([] :: montMul2BodyFuns) (correctionEnv2 xLo xHi yLo yHi) yst
      (.letDecl ["\x00211"] (some (.builtin .sub
        [.var "\x00170", .var "\x00210"]))) =
    .ok (correctionEnv3 xLo xHi yLo yHi, yst, .normal) := by
  simp only [correctionEnv3, correctionEnv2, correctionEnv1, correctionEnv0,
    montMul2OutputEnv, montMul2FactorEnv, montMul2WorkEnv, montMul2StateEnv,
    montMul2InitialEnv]
  rfl

private theorem correctionStmt3 (xLo xHi yLo yHi : U256) (yst : EvmState) :
    Interp.execStmt E 8 ([] :: montMul2BodyFuns) (correctionEnv3 xLo xHi yLo yHi) yst
      (.assign ["\x00171"] (.builtin .sub
        [.builtin .sub [.var "\x00171", .var "\x00209"],
         .builtin .gt [.var "\x00210", .var "\x00170"]])) =
    .ok (correctionEnv4 xLo xHi yLo yHi, yst, .normal) := by
  simp only [correctionEnv4, correctionEnv3, correctionEnv2, correctionEnv1,
    correctionEnv0, montMul2OutputEnv, montMul2FactorEnv, montMul2WorkEnv,
    montMul2StateEnv, montMul2InitialEnv]
  rfl

private theorem correctionStmt4 (xLo xHi yLo yHi : U256) (yst : EvmState) :
    Interp.execStmt E 8 ([] :: montMul2BodyFuns) (correctionEnv4 xLo xHi yLo yHi) yst
      (.assign ["\x00170"] (.var "\x00211")) =
    .ok (correctionEnv5 xLo xHi yLo yHi, yst, .normal) := by
  simp only [correctionEnv5, correctionEnv4, correctionEnv3, correctionEnv2,
    correctionEnv1, correctionEnv0, montMul2OutputEnv, montMul2FactorEnv,
    montMul2WorkEnv, montMul2StateEnv, montMul2InitialEnv]
  rfl

theorem exec_montMul2CorrectionBody (xLo xHi yLo yHi : U256)
    (yst : EvmState) :
    ExecStmt Challenge.YulProof.ClosedEvm.dialect montMul2BodyFuns
      (correctionEnv0 xLo xHi yLo yHi) yst
      (.block
        [.letDecl ["\x00209"] (some (.lit (.number 34565483545414906068789196026815425751))),
         .letDecl ["\x00210"] (some (.lit (.number
          45442060874369865957053122457065728162598490762543039060009208264153100167851))),
         .letDecl ["\x00211"] (some (.builtin .sub [.var "\x00170", .var "\x00210"])),
         .assign ["\x00171"] (.builtin .sub
          [.builtin .sub [.var "\x00171", .var "\x00209"],
           .builtin .gt [.var "\x00210", .var "\x00170"]]),
         .assign ["\x00170"] (.var "\x00211")])
      (restore (correctionEnv0 xLo xHi yLo yHi)
        (correctionEnv5 xLo xHi yLo yHi)) yst .normal := by
  have h0 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (correctionStmt0 xLo xHi yLo yHi yst)
  have h1 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (correctionStmt1 xLo xHi yLo yHi yst)
  have h2 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (correctionStmt2 xLo xHi yLo yHi yst)
  have h3 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (correctionStmt3 xLo xHi yLo yHi yst)
  have h4 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (correctionStmt4 xLo xHi yLo yHi yst)
  have hs := Step.seqCons h0 (Step.seqCons h1
    (Step.seqCons h2 (Step.seqCons h3 (Step.seqCons h4 Step.seqNil))))
  exact Step.block hs

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
