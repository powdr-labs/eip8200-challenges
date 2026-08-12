import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulMiddle

set_option warningAsError true

/-! Executable certificate for the final high word of `fullMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM

def fullMulHighValue (ahi alo bhi blo : U256) : U256 :=
  let middle := fullMulMiddleValue (fullWordValue alo blo).hi
    (fullWordValue ahi blo).lo (fullWordValue alo bhi).lo
  (fullWordValue ahi blo).hi +
    ((fullWordValue alo bhi).hi + (ahi * bhi + middle.carry))

theorem fullMulHighValue_eq (ahi alo bhi blo : U256) :
    fullMulHighValue ahi alo bhi blo =
      (fullMulValue ahi alo bhi blo).r2 := by
  simp [fullMulHighValue, fullMulValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fullMulValue,
    BitVec.add_assoc]

def fullMulFinalBlock : Block Op := fullMulBody.drop 12

def fullMulFinalEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  let middle := fullMulMiddleValue (fullWordValue alo blo).hi
    (fullWordValue ahi blo).lo (fullWordValue alo bhi).lo
  [("\x0065", (fullWordValue alo bhi).hi),
   ("\x0064", (fullWordValue alo bhi).lo),
   ("\x0062", (fullWordValue ahi blo).hi),
   ("\x0061", middle.carry),
   ("\x0059", (fullWordValue alo blo).hi),
   ("\x0052", ahi), ("\x0053", alo), ("\x0054", bhi), ("\x0055", blo),
   ("\x0056", fullMulHighValue ahi alo bhi blo),
   ("\x0057", middle.word), ("\x0058", (fullWordValue alo blo).lo)]

theorem exec_fullMulFinal (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 32 fullMulBodyFuns
      (fullMulMiddleEnv ahi alo bhi blo) yst fullMulFinalBlock =
    .ok (fullMulFinalEnv ahi alo bhi blo, yst, .normal) := by
  rw [Interp.execStmts.eq_def]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
