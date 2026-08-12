import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpModexpDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Staged entry and stores for the frozen G2ADD `fpMul` helper -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem eval_fpMul_args (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fpMulFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] =
    .ok (.vals [ahi, alo, bhi, blo] yst) := by
  rfl

theorem eval_fpMul_of_body (ahi alo bhi blo : U256) (yst final : EvmState)
    (Vend : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hbody : Interp.execStmt Challenge.EvmProof.modexpExec 67 fpMulFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody) =
        .ok (Vend, final, .normal)) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fpMulFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x009" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals
      [(VEnv.get Vend "\x0084").getD 0, (VEnv.get Vend "\x0085").getD 0]
      final) := by
  exact Interp.evalExpr_call_normal
    (eval_fpMul_args ahi alo bhi blo yst) lookup_fpMul (by rfl) hbody

def fpMulProductEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0086", (fullMulValue ahi alo bhi blo).r2),
    ("\x0087", (fullMulValue ahi alo bhi blo).r1),
    ("\x0088", (fullMulValue ahi alo bhi blo).r0)] ++
    fpMulInitialEnv ahi alo bhi blo

private theorem fpMulStmt0_shape : fpMulStmt0 =
    .letDecl ["\x0086", "\x0087", "\x0088"]
      (some (.call "\x006"
        [.var "\x0080", .var "\x0081", .var "\x0082", .var "\x0083"])) := by
  rfl

theorem exec_fpMulStmt0 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulStmt0 =
    .ok (fpMulProductEnv ahi alo bhi blo, yst, .normal) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fpMulBodyFuns
          (fpMulInitialEnv ahi alo bhi blo) yst
          [.var "\x0080", .var "\x0081", .var "\x0082", .var "\x0083"] =
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

/-- The direct stores construct the MODEXP header, product, and exponent byte. -/
theorem exec_fpMulStores (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo) yst
      [fpMulStmt1, fpMulStmt2, fpMulStmt3, fpMulStmt4,
        fpMulStmt5, fpMulStmt6, fpMulStmt7] =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulPreModulusState yst ahi alo bhi blo, .normal) := by
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

