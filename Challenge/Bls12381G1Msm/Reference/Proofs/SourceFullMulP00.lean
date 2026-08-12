import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulValue

set_option warningAsError true

/-! Executable certificate for the low-by-low word product in `fullMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM

abbrev fullWordValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fullWordValue

def fullMulInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0052", ahi), ("\x0053", alo), ("\x0054", bhi), ("\x0055", blo),
   ("\x0056", 0), ("\x0057", 0), ("\x0058", 0)]

def fullMulP00Block : Block Op := fullMulBody.take 3

def fullMulP00Env (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0059", (fullWordValue alo blo).hi),
   ("\x0052", ahi), ("\x0053", alo), ("\x0054", bhi), ("\x0055", blo),
   ("\x0056", 0), ("\x0057", 0),
   ("\x0058", (fullWordValue alo blo).lo)]

theorem exec_fullMulP00 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 32 fullMulBodyFuns
      (fullMulInitialEnv ahi alo bhi blo) yst fullMulP00Block =
    .ok (fullMulP00Env ahi alo bhi blo, yst, .normal) := by
  rw [Interp.execStmts.eq_def]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
