import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddTotal
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceScalarMulRun

set_option warningAsError true

/-! Memory-invariant interface that constructs the concrete G2 scalar trace. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure ScalarMulIterationInvariant (yst : EvmState)
    (bit scalar point out : U256) : Prop where
  doubleInvariant : PointAddMemoryInvariant yst out out out
  addInvariant : scalarMulAddValue scalar bit ≠ 0 →
    ∀ {stdouble : EvmState} {doubleOutcome : Outcome},
      ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
        (pointAddInitialEnv out out out) yst (.block pointAddBody)
        (pointAddInitialEnv out out out) stdouble doubleOutcome →
      (doubleOutcome = .normal ∨ doubleOutcome = .leave) →
      PointAddMemoryInvariant stdouble out out point

theorem step_scalarMulIterationInvariant (yst : EvmState)
    (bit scalar point out : U256)
    (hinvariant : ScalarMulIterationInvariant yst bit scalar point out) :
    ∃ stend,
      ExecStmt Challenge.EvmProof.modexpExec.toDialect
        ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
        (.block scalarMulLoopBody) (scalarMulLoopEnv bit scalar point out)
        stend .normal := by
  obtain ⟨stdouble, doubleOutcome, hdouble, hdoubleOutcome⟩ :=
    step_pointAddTotal yst out out out hinvariant.doubleInvariant
  by_cases hbit : scalarMulAddValue scalar bit = 0
  · exact ⟨stdouble, step_scalarMulLoopBodySkip bit scalar point out
      hdouble hdoubleOutcome hbit⟩
  · obtain ⟨stend, addOutcome, hadd, haddOutcome⟩ :=
      step_pointAddTotal stdouble out out point
        (hinvariant.addInvariant hbit hdouble hdoubleOutcome)
    exact ⟨stend, step_scalarMulLoopBodyTaken bit scalar point out
      hdouble hdoubleOutcome hbit hadd haddOutcome⟩

def ScalarMulInvariantSchedule (scalar point out : U256) :
    Nat → U256 → EvmState → Prop
  | 0, bit, _ => bit = 0
  | n + 1, bit, yst =>
      bit ≠ 0 ∧
      ScalarMulIterationInvariant yst bit scalar point out ∧
      ∀ stmid,
        ExecStmt Challenge.EvmProof.modexpExec.toDialect
          ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
          (.block scalarMulLoopBody) (scalarMulLoopEnv bit scalar point out)
          stmid .normal →
        ScalarMulInvariantSchedule scalar point out n
          (scalarMulNextBit bit) stmid

theorem scalarMulTrace_of_invariant {n : Nat}
    {bit scalar point out : U256} {yst : EvmState}
    (hinvariant : ScalarMulInvariantSchedule scalar point out n bit yst) :
    ∃ stend, ScalarMulTrace scalar point out n bit yst stend := by
  induction n generalizing bit yst with
  | zero =>
    have hzero : bit = 0 := hinvariant
    subst bit
    exact ⟨yst, ScalarMulTrace.done yst⟩
  | succ n ih =>
    obtain ⟨hbit, hiteration, htail⟩ := hinvariant
    obtain ⟨stmid, hbody⟩ :=
      step_scalarMulIterationInvariant yst bit scalar point out hiteration
    obtain ⟨stend, htrace⟩ := ih (htail stmid hbody)
    exact ⟨stend, ScalarMulTrace.step hbit hbody htrace⟩

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
