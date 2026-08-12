import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulP10

set_option warningAsError true

/-! Executable certificate for the low-by-high word product in `fullMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM

def fullMulP01Block : Block Op := (fullMulBody.drop 6).take 3

def fullMulP01Env (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0065", (fullWordValue alo bhi).hi),
   ("\x0064", (fullWordValue alo bhi).lo),
   ("\x0062", (fullWordValue ahi blo).hi),
   ("\x0061", (fullWordValue ahi blo).lo),
   ("\x0059", (fullWordValue alo blo).hi),
   ("\x0052", ahi), ("\x0053", alo), ("\x0054", bhi), ("\x0055", blo),
   ("\x0056", 0), ("\x0057", 0),
   ("\x0058", (fullWordValue alo blo).lo)]

theorem exec_fullMulP01 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 32 fullMulBodyFuns
      (fullMulP10Env ahi alo bhi blo) yst fullMulP01Block =
    .ok (fullMulP01Env ahi alo bhi blo, yst, .normal) := by
  rw [Interp.execStmts.eq_def]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
