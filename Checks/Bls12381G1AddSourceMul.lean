import Challenge.Bls12381G1Add.Reference.Proofs.SourceMul

set_option warningAsError true

open YulSemantics YulSemantics.EVM

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

example (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x006" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fullMulValue ahi alo bhi blo).r2,
      (fullMulValue ahi alo bhi blo).r1,
      (fullMulValue ahi alo bhi blo).r0] yst) :=
  eval_fullMul ahi alo bhi blo yst

example (ahi alo bhi blo : U256) :
    convFullMul (fullMulValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.schoolbookProduct
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  conv_fullMulValue ahi alo bhi blo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fullMul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_fullMul

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullWordValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fullWordValue

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullWordValue_hi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fullWordValue_hi

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullWordValue_lo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fullWordValue_lo

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullMulMiddleValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fullMulMiddleValue

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullMulMiddleValue_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fullMulMiddleValue_word

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullMulMiddleValue_carry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fullMulMiddleValue_carry

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fullMulValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conv_fullMulValue

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
