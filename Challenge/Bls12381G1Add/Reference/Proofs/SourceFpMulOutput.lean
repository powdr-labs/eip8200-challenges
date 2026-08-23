import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulCall

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` output loads -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpMulHighEnv (yst : EvmState) (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpMulProductEnv ahi alo bhi blo) ["\x0072"]
    [(fpMulResult yst ahi alo bhi blo).1]

def fpMulReturnEnv (yst : EvmState) (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpMulHighEnv yst ahi alo bhi blo) ["\x0073"]
    [(fpMulResult yst ahi alo bhi blo).2]

/-- The final two source statements load the returned high and low limbs in
their exact order and update both memory high-water marks. -/
theorem exec_fpMulOutput (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 56 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulCallState yst ahi alo bhi blo) [fpMulStmt10, fpMulStmt11] =
    .ok (fpMulReturnEnv yst ahi alo bhi blo,
      fpMulFinalState yst ahi alo bhi blo, .normal) := by
  rfl

theorem fpMulReturnEnv_hi (yst : EvmState) (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulReturnEnv yst ahi alo bhi blo) "\x0072").getD 0 =
      (fpMulResult yst ahi alo bhi blo).1 := by
  rfl

theorem fpMulReturnEnv_lo (yst : EvmState) (ahi alo bhi blo : U256) :
    (VEnv.get (fpMulReturnEnv yst ahi alo bhi blo) "\x0073").getD 0 =
      (fpMulResult yst ahi alo bhi blo).2 := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
