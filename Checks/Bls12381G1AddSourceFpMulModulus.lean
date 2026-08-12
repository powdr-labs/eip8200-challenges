import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulModulus

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 57 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulPreModulusState yst ahi alo bhi blo) fpMulStmt8 =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulInputState yst ahi alo bhi blo, .normal) :=
  exec_fpMulModulus ahi alo bhi blo yst

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpMulModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulModulus

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
