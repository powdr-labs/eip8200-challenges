import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulBody

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fpMulFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody) =
    .ok (fpMulBodyResultEnv yst ahi alo bhi blo,
      fpMulFinalState yst ahi alo bhi blo, .normal) :=
  exec_fpMulBody ahi alo bhi blo yst

example (ahi alo bhi blo : U256) (yst : EvmState) :
    (VEnv.get (fpMulBodyResultEnv yst ahi alo bhi blo) "\x0072").getD 0 =
      (fpMulResult yst ahi alo bhi blo).1 :=
  fpMulBodyResultEnv_hi yst ahi alo bhi blo

example (ahi alo bhi blo : U256) (yst : EvmState) :
    (VEnv.get (fpMulBodyResultEnv yst ahi alo bhi blo) "\x0073").getD 0 =
      (fpMulResult yst ahi alo bhi blo).2 :=
  fpMulBodyResultEnv_lo yst ahi alo bhi blo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpMulBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulBody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulBodyResultEnv_hi' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulBodyResultEnv_hi

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulBodyResultEnv_lo' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulBodyResultEnv_lo

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
