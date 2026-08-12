import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStart

set_option warningAsError true

/-! # First frozen G1ADD `fpMul` statement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpMulProductEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0074", (fullMulValue ahi alo bhi blo).r2),
    ("\x0075", (fullMulValue ahi alo bhi blo).r1),
    ("\x0076", (fullMulValue ahi alo bhi blo).r0)] ++
    fpMulInitialEnv ahi alo bhi blo

private theorem fpMulStmt0_shape : fpMulStmt0 =
    .letDecl ["\x0074", "\x0075", "\x0076"]
      (some (.call "\x006"
        [.var "\x0068", .var "\x0069", .var "\x0070", .var "\x0071"])) := by
  rfl

/-- The first source statement evaluates the already-certified full-word
schoolbook helper once and binds its three result words. -/
theorem exec_fpMulStmt0 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulStmt0 =
    .ok (fpMulProductEnv ahi alo bhi blo, yst, .normal) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fpMulBodyFuns
          (fpMulInitialEnv ahi alo bhi blo) yst
          [.var "\x0068", .var "\x0069", .var "\x0070", .var "\x0071"] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 63 fpMulFuns
          [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hlookup : lookupFun fpMulBodyFuns "\x006" =
      lookupFun fpMulFuns "\x006" := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x006") hargs hlookup
  rw [fpMulStmt0_shape, Interp.execStmt, hcall]
  rw [show fpMulFuns =
    [hoist Challenge.EvmProof.modexpExec.toDialect
      Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fullMul ahi alo bhi blo yst]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
