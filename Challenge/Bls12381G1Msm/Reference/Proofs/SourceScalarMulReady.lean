import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddTotal
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulBody

set_option warningAsError true

/-! Memory-readiness interface that constructs the concrete scalar trace. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure ScalarMulIterationReady (yst : EvmState)
    (bit scalar point out : U256) : Prop where
  doubleReady : PointAddReady yst out out out
  addReady : scalar &&& bit ≠ 0 →
    ∀ {Vdouble : VEnv Challenge.EvmProof.modexpExec.toDialect}
      {stdouble : EvmState} {odouble : Outcome},
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out out out) yst pointAddBody
        Vdouble stdouble odouble →
      (odouble = .normal ∨ odouble = .leave) →
      PointAddReady stdouble out out point

theorem step_scalarMulIterationReady (yst : EvmState)
    (bit scalar point out : U256)
    (hready : ScalarMulIterationReady yst bit scalar point out) :
    ∃ stend,
      ExecStmt Challenge.EvmProof.modexpExec.toDialect
        ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
        (.block scalarMulLoopBody) (scalarMulLoopEnv bit scalar point out)
        stend .normal := by
  obtain ⟨Vdouble, stdouble, odouble, hdouble, hodouble⟩ :=
    step_pointAddTotal yst out out out hready.doubleReady
  by_cases hbit : scalar &&& bit = 0
  · exact ⟨stdouble, step_scalarMulLoopBodySkip bit scalar point out hbit
      hdouble hodouble⟩
  · obtain ⟨Vend, stend, oadd, hadd, hoadd⟩ :=
      step_pointAddTotal stdouble out out point
        (hready.addReady hbit hdouble hodouble)
    exact ⟨stend, step_scalarMulLoopBodyTaken bit scalar point out hbit
      hdouble hodouble hadd hoadd⟩

def ScalarMulReadySchedule (scalar point out : U256) :
    Nat → U256 → EvmState → Prop
  | 0, bit, _ => bit = 0
  | n + 1, bit, yst =>
      bit ≠ 0 ∧
      ScalarMulIterationReady yst bit scalar point out ∧
      ∀ stmid,
        ExecStmt Challenge.EvmProof.modexpExec.toDialect
          ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
          (.block scalarMulLoopBody) (scalarMulLoopEnv bit scalar point out)
          stmid .normal →
        ScalarMulReadySchedule scalar point out n (scalarMulNextBit bit) stmid

theorem scalarMulTrace_of_ready {n : Nat} {bit scalar point out : U256}
    {yst : EvmState}
    (hready : ScalarMulReadySchedule scalar point out n bit yst) :
    ∃ stend, ScalarMulTrace scalar point out n bit yst stend := by
  induction n generalizing bit yst with
  | zero =>
    have hzero : bit = 0 := hready
    subst bit
    exact ⟨yst, ScalarMulTrace.done yst⟩
  | succ n ih =>
    obtain ⟨hbit, hiteration, htail⟩ := hready
    obtain ⟨stmid, hbody⟩ :=
      step_scalarMulIterationReady yst bit scalar point out hiteration
    obtain ⟨stend, htrace⟩ := ih (htail stmid hbody)
    exact ⟨stend, ScalarMulTrace.step hbit hbody htrace⟩

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
