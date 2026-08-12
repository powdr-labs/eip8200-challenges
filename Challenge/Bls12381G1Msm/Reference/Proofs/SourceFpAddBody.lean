import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddCorrect

set_option warningAsError true

/-! Relational composition of the staged G1MSM `fpAdd` body. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt modexpExec.toDialect funs V st stmt V' st' outcome :=
  (Interp.sound_all_of
    (E := modexpExec)
    (fun _ _ _ _ hbuiltin => modexpBuiltinFn_sound hbuiltin) n).2.2.1
    _ _ _ _ _ _ _ h

def fpAddFinalEnv (ahi alo bhi blo : U256) :
    VEnv modexpExec.toDialect :=
  if fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) = (0#256) then
    fpAddHighEnv ahi alo bhi blo
  else fpAddCorrectEnv ahi alo bhi blo

theorem step_fpAddBody (ahi alo bhi blo : U256) (yst : EvmState) :
    ExecStmts modexpExec.toDialect fpAddBodyFuns
      (fpAddInitialEnv ahi alo bhi blo) yst fpAddBody
      (fpAddFinalEnv ahi alo bhi blo) yst .normal := by
  have h0 := sound_execStmt (exec_fpAddStmt0 ahi alo bhi blo yst)
  have h1 := sound_execStmt (exec_fpAddStmt1 ahi alo bhi blo yst)
  by_cases hcondition : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) = (0#256)
  · have h2 := sound_execStmt
      (exec_fpAddStmt2_keep ahi alo bhi blo yst hcondition)
    simpa [fpAddBody, fpAddFinalEnv, hcondition] using
      Step.seqCons h0 (Step.seqCons h1 (Step.seqCons h2 Step.seqNil))
  · have h2 := sound_execStmt
      (exec_fpAddStmt2_correct ahi alo bhi blo yst hcondition)
    simpa [fpAddBody, fpAddFinalEnv, hcondition] using
      Step.seqCons h0 (Step.seqCons h1 (Step.seqCons h2 Step.seqNil))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
