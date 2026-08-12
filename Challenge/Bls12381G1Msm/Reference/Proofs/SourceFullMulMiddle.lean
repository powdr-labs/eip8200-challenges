import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulP01

set_option warningAsError true

/-! Executable certificate for the middle-word carry schedule in `fullMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM

abbrev fullMulMiddleValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fullMulMiddleValue

def fullMulMiddleBlock : Block Op := (fullMulBody.drop 9).take 3

def fullMulMiddleEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  let middle := fullMulMiddleValue (fullWordValue alo blo).hi
    (fullWordValue ahi blo).lo (fullWordValue alo bhi).lo
  [("\x0065", (fullWordValue alo bhi).hi),
   ("\x0064", (fullWordValue alo bhi).lo),
   ("\x0062", (fullWordValue ahi blo).hi),
   ("\x0061", middle.carry),
   ("\x0059", (fullWordValue alo blo).hi),
   ("\x0052", ahi), ("\x0053", alo), ("\x0054", bhi), ("\x0055", blo),
   ("\x0056", 0), ("\x0057", middle.word),
   ("\x0058", (fullWordValue alo blo).lo)]

theorem exec_fullMulMiddle (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 64 fullMulBodyFuns
      (fullMulP01Env ahi alo bhi blo) yst fullMulMiddleBlock =
    .ok (fullMulMiddleEnv ahi alo bhi blo, yst, .normal) := by
  rw [Interp.execStmts.eq_def]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
