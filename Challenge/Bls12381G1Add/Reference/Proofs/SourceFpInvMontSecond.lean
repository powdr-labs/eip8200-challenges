import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMontAccumulate
import Challenge.YulProof.Interpreter

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev E := Challenge.YulProof.ClosedEvm.exec

private theorem montMul2Stmt8_shape : montMul2Stmt8 = .block
    [.letDecl ["\x00199"] (some (.lit (.number
      45442060874369865957053122457065728162598490762543039060009208264153100167851))),
     .letDecl ["\x00200"] (some (.builtin .mul [.var "\x00180", .var "\x00199"])),
     .letDecl ["\x00201"] (some (.builtin .mulmod
      [.var "\x00180", .var "\x00199", .builtin .not [.lit (.number 0)]])),
     .letDecl ["\x00202"] (some (.builtin .sub
      [.builtin .sub [.var "\x00201", .var "\x00200"],
       .builtin .lt [.var "\x00201", .var "\x00200"]])),
     .letDecl ["\x00203"] (some (.builtin .add [.var "\x00172", .var "\x00200"])),
     .letDecl ["\x00204"] (some (.builtin .add
      [.var "\x00202", .builtin .lt [.var "\x00203", .var "\x00172"]])),
     .letDecl ["\x00205"] (some (.lit (.number 34565483545414906068789196026815425751))),
     .assign ["\x00200"] (.builtin .mul [.var "\x00180", .var "\x00205"]),
     .assign ["\x00201"] (.builtin .mulmod
      [.var "\x00180", .var "\x00205", .builtin .not [.lit (.number 0)]]),
     .assign ["\x00202"] (.builtin .sub
      [.builtin .sub [.var "\x00201", .var "\x00200"],
       .builtin .lt [.var "\x00201", .var "\x00200"]]),
     .assign ["\x00203"] (.builtin .add [.var "\x00173", .var "\x00200"]),
     .letDecl ["\x00206"] (some (.builtin .lt [.var "\x00203", .var "\x00173"])),
     .letDecl ["\x00207"] (some (.builtin .add [.var "\x00203", .var "\x00204"])),
     .letDecl ["\x00208"] (some (.builtin .lt [.var "\x00207", .var "\x00203"])),
     .assign ["\x00170"] (.var "\x00207"),
     .assign ["\x00171"] (.builtin .add
        [.var "\x00174", .builtin .add [.var "\x00202",
          .builtin .add [.var "\x00206", .var "\x00208"]]])] := by
  rfl

set_option maxHeartbeats 800000 in
theorem interp_montMul2_secondReduce (xLo xHi yLo yHi : U256)
    (yst : EvmState) :
    Interp.execStmt E 40 montMul2BodyFuns
      (montMul2FactorEnv (montMul2InitialEnv xLo xHi yLo yHi)
        (montAccumulated xLo xHi yLo yHi)) yst montMul2Stmt8 =
    .ok (montMul2OutputEnv (montMul2InitialEnv xLo xHi yLo yHi)
      (montAccumulated xLo xHi yLo yHi)
      (montSecond xLo xHi yLo yHi), yst, .normal) := by
  rw [montMul2Stmt8_shape]
  simp only [montSecond, montAccumulated, montFirst, montInitial]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
