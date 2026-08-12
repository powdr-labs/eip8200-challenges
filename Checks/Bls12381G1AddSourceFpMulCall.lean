import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulCall

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 56 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulInputState yst ahi alo bhi blo) fpMulStmt9 =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulCallState yst ahi alo bhi blo, .normal) :=
  exec_fpMulCall ahi alo bhi blo yst

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpMulCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulCall

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
