import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulOutput

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 56 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulCallState yst ahi alo bhi blo) [fpMulStmt10, fpMulStmt11] =
    .ok (fpMulReturnEnv yst ahi alo bhi blo,
      fpMulFinalState yst ahi alo bhi blo, .normal) :=
  exec_fpMulOutput ahi alo bhi blo yst

example (ahi alo bhi blo : U256) (yst : EvmState) :
    (VEnv.get (fpMulReturnEnv yst ahi alo bhi blo) "\x0072").getD 0 =
      (fpMulResult yst ahi alo bhi blo).1 :=
  fpMulReturnEnv_hi yst ahi alo bhi blo

example (ahi alo bhi blo : U256) (yst : EvmState) :
    (VEnv.get (fpMulReturnEnv yst ahi alo bhi blo) "\x0073").getD 0 =
      (fpMulResult yst ahi alo bhi blo).2 :=
  fpMulReturnEnv_lo yst ahi alo bhi blo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_fpMulOutput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_fpMulOutput

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulReturnEnv_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fpMulReturnEnv_hi

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulReturnEnv_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fpMulReturnEnv_lo

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
