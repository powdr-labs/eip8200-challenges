import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStores

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo) yst
      [fpMulStmt1, fpMulStmt2, fpMulStmt3, fpMulStmt4,
        fpMulStmt5, fpMulStmt6, fpMulStmt7] =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulPreModulusState yst ahi alo bhi blo, .normal) :=
  exec_fpMulStores ahi alo bhi blo yst

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpMulStores' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulStores

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
