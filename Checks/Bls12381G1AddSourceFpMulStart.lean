import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStart

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : fpMulBody =
    [fpMulStmt0, fpMulStmt1, fpMulStmt2, fpMulStmt3,
      fpMulStmt4, fpMulStmt5, fpMulStmt6, fpMulStmt7,
      fpMulStmt8, fpMulStmt9, fpMulStmt10, fpMulStmt11] :=
  fpMulBody_eq

example : hoist Challenge.EvmProof.modexpExec.toDialect fpMulBody = [] :=
  hoist_fpMulBody

example : hoist Challenge.EvmProof.modexpExec.toDialect fpMulBody :: fpMulFuns =
    fpMulBodyFuns :=
  fpMulBodyFuns_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulBody_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpMulBody_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.hoist_fpMulBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hoist_fpMulBody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulBodyFuns_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fpMulBodyFuns_eq

example (ahi alo bhi blo : U256) (yst final : EvmState)
    (Vend : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hbody : Interp.execStmt Challenge.EvmProof.modexpExec 67 fpMulFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody) =
        .ok (Vend, final, .normal)) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fpMulFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals
      [(VEnv.get Vend "\x0072").getD 0, (VEnv.get Vend "\x0073").getD 0]
      final) :=
  eval_fpMul_of_body ahi alo bhi blo yst final Vend hbody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpMul_of_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fpMul_of_body

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
