import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpMulDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Staged entry and stores for the frozen G2MSM `fpMul` helper. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

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
      [(VEnv.get Vend "\x0090").getD 0, (VEnv.get Vend "\x0091").getD 0]
      final) := by
  exact Interp.evalExpr_call_normal
    (eval_fpMul_args ahi alo bhi blo yst) lookup_fpMul (by rfl) hbody

def fpMulProductEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0092", (fullMulValue ahi alo bhi blo).r2),
    ("\x0093", (fullMulValue ahi alo bhi blo).r1),
    ("\x0094", (fullMulValue ahi alo bhi blo).r0)] ++
    fpMulInitialEnv ahi alo bhi blo

private theorem fpMulStmt0_shape : fpMulStmt0 =
    .letDecl ["\x0092", "\x0093", "\x0094"]
      (some (.call "\x006"
        [.var "\x0086", .var "\x0087", .var "\x0088", .var "\x0089"])) := by
  rfl

theorem exec_fpMulStmt0 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulStmt0 =
    .ok (fpMulProductEnv ahi alo bhi blo, yst, .normal) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 63 fpMulBodyFuns
          (fpMulInitialEnv ahi alo bhi blo) yst
          [.var "\x0086", .var "\x0087", .var "\x0088", .var "\x0089"] =
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

theorem exec_fpMulStores (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo) yst
      [fpMulStmt1, fpMulStmt2, fpMulStmt3, fpMulStmt4,
        fpMulStmt5, fpMulStmt6, fpMulStmt7] =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulPreModulusState yst ahi alo bhi blo, .normal) := by
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
