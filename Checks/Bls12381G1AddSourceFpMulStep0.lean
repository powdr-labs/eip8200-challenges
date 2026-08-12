import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStep0

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulStmt0 =
    .ok (fpMulProductEnv ahi alo bhi blo, yst, .normal) :=
  exec_fpMulStmt0 ahi alo bhi blo yst

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpMulStmt0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulStmt0

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
