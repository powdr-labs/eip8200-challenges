import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulOutput

set_option warningAsError true

/-! # Complete frozen G1ADD `fpMul` body -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpMulBodyResultEnv (yst : EvmState) (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fpMulInitialEnv ahi alo bhi blo)
    (fpMulReturnEnv yst ahi alo bhi blo)

/-- The twelve independently checked source statements compose to the
normally completed frozen `fpMul` body. -/
theorem exec_fpMulBody (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fpMulFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulBody) =
    .ok (fpMulBodyResultEnv yst ahi alo bhi blo,
      fpMulFinalState yst ahi alo bhi blo, .normal) := by
  have hcallOutput :
      Interp.execStmts Challenge.EvmProof.modexpExec 57 fpMulBodyFuns
          (fpMulProductEnv ahi alo bhi blo)
          (fpMulInputState yst ahi alo bhi blo)
          [fpMulStmt9, fpMulStmt10, fpMulStmt11] =
        .ok (fpMulReturnEnv yst ahi alo bhi blo,
          fpMulFinalState yst ahi alo bhi blo, .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fpMulCall ahi alo bhi blo yst)
      (exec_fpMulOutput ahi alo bhi blo yst)
  have hmodulusTail :
      Interp.execStmts Challenge.EvmProof.modexpExec 58 fpMulBodyFuns
          (fpMulProductEnv ahi alo bhi blo)
          (fpMulPreModulusState yst ahi alo bhi blo)
          [fpMulStmt8, fpMulStmt9, fpMulStmt10, fpMulStmt11] =
        .ok (fpMulReturnEnv yst ahi alo bhi blo,
          fpMulFinalState yst ahi alo bhi blo, .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fpMulModulus ahi alo bhi blo yst) hcallOutput
  have hstoresTail :
      Interp.execStmts Challenge.EvmProof.modexpExec 65 fpMulBodyFuns
          (fpMulProductEnv ahi alo bhi blo) yst
          [fpMulStmt1, fpMulStmt2, fpMulStmt3, fpMulStmt4,
            fpMulStmt5, fpMulStmt6, fpMulStmt7, fpMulStmt8,
            fpMulStmt9, fpMulStmt10, fpMulStmt11] =
        .ok (fpMulReturnEnv yst ahi alo bhi blo,
          fpMulFinalState yst ahi alo bhi blo, .normal) := by
    exact Interp.execStmts_append_normal (E := Challenge.EvmProof.modexpExec)
        (n := 58) (pre := [fpMulStmt1, fpMulStmt2, fpMulStmt3, fpMulStmt4,
          fpMulStmt5, fpMulStmt6, fpMulStmt7])
        (tail := [fpMulStmt8, fpMulStmt9, fpMulStmt10, fpMulStmt11])
        (by omega) (exec_fpMulStores ahi alo bhi blo yst) hmodulusTail
  have hbody :
      Interp.execStmts Challenge.EvmProof.modexpExec 66 fpMulBodyFuns
          (fpMulInitialEnv ahi alo bhi blo) yst
          [fpMulStmt0, fpMulStmt1, fpMulStmt2, fpMulStmt3,
            fpMulStmt4, fpMulStmt5, fpMulStmt6, fpMulStmt7,
            fpMulStmt8, fpMulStmt9, fpMulStmt10, fpMulStmt11] =
        .ok (fpMulReturnEnv yst ahi alo bhi blo,
          fpMulFinalState yst ahi alo bhi blo, .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fpMulStmt0 ahi alo bhi blo yst) hstoresTail
  rw [Interp.execStmt, fpMulBodyFuns_eq, fpMulBody_eq, hbody]
  rfl

theorem fpMulBodyResultEnv_hi (yst : EvmState) (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulBodyResultEnv yst ahi alo bhi blo) "\x0072").getD 0 =
      (fpMulResult yst ahi alo bhi blo).1 := by
  rfl

theorem fpMulBodyResultEnv_lo (yst : EvmState) (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulBodyResultEnv yst ahi alo bhi blo) "\x0073").getD 0 =
      (fpMulResult yst ahi alo bhi blo).2 := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
