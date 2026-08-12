import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpMulResult yst ahi alo bhi blo).1,
      (fpMulResult yst ahi alo bhi blo).2]
      (fpMulFinalState yst ahi alo bhi blo)) :=
  eval_fpMul ahi alo bhi blo yst

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpMul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpMul

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
