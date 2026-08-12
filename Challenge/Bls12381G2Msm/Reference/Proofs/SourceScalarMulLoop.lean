import Challenge.Bls12381G2Msm.Reference.Proofs.SourceScalarMulCalls

set_option warningAsError true

/-! Structural execution of the frozen 256-bit G2 scalar loop from a trace. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

inductive ScalarMulTrace (scalar point out : U256) :
    Nat → U256 → EvmState → EvmState → Prop
  | done (yst : EvmState) : ScalarMulTrace scalar point out 0 0 yst yst
  | step {n : Nat} {bit : U256} {yst stmid stend : EvmState}
      (hbit : bit ≠ 0)
      (hbody : ExecStmt Challenge.EvmProof.modexpExec.toDialect
        ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
        (.block scalarMulLoopBody) (scalarMulLoopEnv bit scalar point out)
        stmid .normal)
      (htail : ScalarMulTrace scalar point out n (scalarMulNextBit bit)
        stmid stend) :
      ScalarMulTrace scalar point out (n + 1) bit yst stend

theorem step_scalarMulLoop {n : Nat} {bit scalar point out : U256}
    {yst stend : EvmState}
    (htrace : ScalarMulTrace scalar point out n bit yst stend) :
    ExecLoop Challenge.EvmProof.modexpExec.toDialect
      ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
      scalarMulLoopCondition scalarMulLoopPost scalarMulLoopBody
      (scalarMulLoopEnv 0 scalar point out) stend .normal := by
  induction htrace with
  | done yst =>
    exact Step.loopDone
      (step_scalarMulLoopCondition _ yst 0 scalar point out) rfl
  | step hbit hbody htail ih =>
    exact Step.loopStep
      (step_scalarMulLoopCondition _ _ _ scalar point out) hbit hbody
      (Or.inl rfl)
      (step_scalarMulLoopPost _ _ scalar point out) ih

private theorem scalarMulStmt2_eq : scalarMulStmt2 =
    .forLoop scalarMulLoopInit scalarMulLoopCondition
      scalarMulLoopPost scalarMulLoopBody := by rfl

theorem step_scalarMulFor (scalar point out : U256) {yst stend : EvmState}
    (htrace : ScalarMulTrace scalar point out 256 scalarMulInitialBit
      yst stend) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulLoopEnv scalarMulInitialBit scalar point out) yst
      scalarMulStmt2 (scalarMulLoopEnv 0 scalar point out)
      stend .normal := by
  rw [scalarMulStmt2_eq]
  have hloop := step_scalarMulLoop htrace
  have hfor : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      scalarMulBodyFuns
      (scalarMulLoopEnv scalarMulInitialBit scalar point out) yst
      (.forLoop scalarMulLoopInit scalarMulLoopCondition
        scalarMulLoopPost scalarMulLoopBody)
      (restore (scalarMulLoopEnv scalarMulInitialBit scalar point out)
        (scalarMulLoopEnv 0 scalar point out)) stend .normal := by
    apply Step.forLoop
    · rw [scalarMulLoopInit_eq]
      exact Step.seqNil
    · rw [show hoist Challenge.EvmProof.modexpExec.toDialect
        scalarMulLoopInit = [] by rfl]
      simpa [scalarMulLoopEnv] using hloop
  simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hfor

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
