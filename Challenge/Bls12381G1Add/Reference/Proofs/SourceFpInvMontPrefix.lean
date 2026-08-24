import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvExecDefs
import Challenge.YulProof.Interpreter

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev E := Challenge.YulProof.ClosedEvm.exec

theorem interp_montMul2_prefix (xLo xHi yLo yHi : U256) (yst : EvmState) :
    Interp.execStmts E 40 montMul2BodyFuns
      (montMul2InitialEnv xLo xHi yLo yHi) yst
      [montMul2Stmt0, montMul2Stmt1, montMul2Stmt2, montMul2Stmt3] =
    .ok (montMul2StateEnv (montMul2InitialEnv xLo xHi yLo yHi)
      (montInitial xLo yLo yHi), yst, .normal) := by
  simp only [montInitial]
  rfl

theorem interp_montMul2_firstReduce (xLo xHi yLo yHi : U256)
    (yst : EvmState) :
    Interp.execStmts E 40 montMul2BodyFuns
      (montMul2StateEnv (montMul2InitialEnv xLo xHi yLo yHi)
        (montInitial xLo yLo yHi)) yst
      [montMul2Stmt4, montMul2Stmt5] =
    .ok (montMul2WorkEnv (montMul2InitialEnv xLo xHi yLo yHi)
      (montMul2FactorValue (montInitial xLo yLo yHi))
      (montFirst xLo yLo yHi), yst, .normal) := by
  simp only [montFirst, montInitial]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
