import Challenge.Bls12381G2Msm.Reference.Proofs.SourceScalarMulInit
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Loop-condition and right-shift boundaries for naive G2 scalar multiplication. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def scalarMulNextBit (bit : U256) : U256 := bit >>> 1

theorem step_scalarMulLoopCondition (funs) (yst : EvmState)
    (bit scalar point out : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (scalarMulLoopEnv bit scalar point out) yst scalarMulLoopCondition
      (.vals [bit] yst) := by
  rw [scalarMulLoopCondition_eq]
  exact Step.var rfl

private theorem exec_scalarMulLoopPost (yst : EvmState)
    (bit scalar point out : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 30
      ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
      (.block scalarMulLoopPost) =
    .ok (scalarMulLoopEnv (scalarMulNextBit bit) scalar point out,
      yst, .normal) := by
  rfl

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

theorem step_scalarMulLoopPost (yst : EvmState)
    (bit scalar point out : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      (.block scalarMulLoopPost)
      (scalarMulLoopEnv (scalarMulNextBit bit) scalar point out)
      yst .normal :=
  soundStmt (exec_scalarMulLoopPost yst bit scalar point out)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
