import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleStmt0Exec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleStmt1Exec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleStmt2Exec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleStmt3Exec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleMulExec
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Frozen G1ADD equal-point doubling-slope execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.YulProof.ClosedEvm.exec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.YulProof.ClosedEvm.exec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.YulProof.ClosedEvm.exec)
    (fun _ _ _ _ hbuiltin =>
      (Challenge.YulProof.ClosedEvm.exec_lawful _ _ _ _).mpr hbuiltin) n).2.2.1
    funs V st stmt V' st' outcome h

/-- The complete six-statement source doubling-slope schedule executes to the
exact lambda words. -/
theorem step_mainFiniteDoubleBody (yst : EvmState)
    (hden : Fp.Canonical (fpInvInputLimbs
      (mainFiniteDoubleDenominatorWords yst).1
      (mainFiniteDoubleDenominatorWords yst).2)) :
    ExecStmts Challenge.YulProof.ClosedEvm.exec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      mainFiniteDoubleBody (mainFiniteDoubleEnv6 yst)
      (mainFiniteDoubleFinalState yst) .normal := by
  rw [mainFiniteDoubleBody_eq]
  exact Step.seqCons (step_mainFiniteDoubleStmt0 yst)
    (Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt1 yst))
      (Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt2 yst))
        (Step.seqCons (step_mainFiniteDoubleStmt3 yst)
          (Step.seqCons
            (step_mainFiniteDoubleStmt4 yst hden)
            (Step.seqCons (sound_execStmt (exec_mainFiniteDoubleStmt5 yst))
              Step.seqNil)))))

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
