import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMontPrefix
import Challenge.YulProof.Interpreter

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev E := Challenge.YulProof.ClosedEvm.exec

theorem interp_montMul2_accumulate (xLo xHi yLo yHi : U256)
    (yst : EvmState) :
    Interp.execStmt E 40 montMul2BodyFuns
      (montMul2WorkEnv (montMul2InitialEnv xLo xHi yLo yHi)
        (montMul2FactorValue (montInitial xLo yLo yHi))
        (montFirst xLo yLo yHi)) yst montMul2Stmt6 =
    .ok (montMul2WorkEnv (montMul2InitialEnv xLo xHi yLo yHi)
      (montMul2FactorValue (montInitial xLo yLo yHi))
      (montAccumulated xLo xHi yLo yHi), yst, .normal) := by
  simp only [montAccumulated, montFirst, montInitial]
  rfl

theorem interp_montMul2_secondFactor (xLo xHi yLo yHi : U256)
    (yst : EvmState) :
    Interp.execStmt E 40 montMul2BodyFuns
      (montMul2WorkEnv (montMul2InitialEnv xLo xHi yLo yHi)
        (montMul2FactorValue (montInitial xLo yLo yHi))
        (montAccumulated xLo xHi yLo yHi)) yst montMul2Stmt7 =
    .ok (montMul2FactorEnv (montMul2InitialEnv xLo xHi yLo yHi)
      (montAccumulated xLo xHi yLo yHi), yst, .normal) := by
  simp only [montAccumulated, montFirst, montInitial]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
