import Challenge.Bls12381G2Msm.Reference.Proofs.SourceScalarMulDefs

set_option warningAsError true

/-! Exact initialization of the frozen naive G2 scalar multiplier. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def scalarMulInitialBit : U256 :=
  EVM.litValue (.number
    57896044618658097711785492504343953926634992332820282019728792003956564819968)

def scalarMulLoopEnv (bit scalar point out : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00151", bit)] ++ scalarMulInitialEnv scalar point out

def scalarMulInitState (yst : EvmState) (out : U256) : EvmState :=
  msmStoreInfinityState yst out

private theorem scalarMulStmt0_eq : scalarMulStmt0 =
    .exprStmt (.call "\x0026" [.var "\x00150"]) := by rfl

private theorem scalarMulStmt1_eq : scalarMulStmt1 =
    .letDecl ["\x00151"]
      (some (.builtin .shl
        [.lit (.number 255), .lit (.number 1)])) := by
  rfl

private theorem step_scalarMulStoreInfinity (yst : EvmState)
    (scalar point out : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) yst scalarMulStmt0
      (scalarMulInitialEnv scalar point out)
      (scalarMulInitState yst out) .normal := by
  rw [scalarMulStmt0_eq]
  have hout : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      scalarMulBodyFuns (scalarMulInitialEnv scalar point out) yst
      (.var "\x00150") (.vals [out] yst) := Step.var rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      scalarMulBodyFuns (scalarMulInitialEnv scalar point out) yst
      [.var "\x00150"] (.vals [out] yst) :=
    Step.argsCons Step.argsNil hout
  exact Step.exprStmt (step_msmStoreInfinity_of_args out hargs (by rfl))

private theorem step_scalarMulInitialBit (yst : EvmState)
    (scalar point out : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) (scalarMulInitState yst out)
      scalarMulStmt1 (scalarMulLoopEnv scalarMulInitialBit scalar point out)
      (scalarMulInitState yst out) .normal := by
  rw [scalarMulStmt1_eq]
  have h255 : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      scalarMulBodyFuns (scalarMulInitialEnv scalar point out)
      (scalarMulInitState yst out) (.lit (.number 255))
      (.vals [255] (scalarMulInitState yst out)) := Step.lit
  have hone : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      scalarMulBodyFuns (scalarMulInitialEnv scalar point out)
      (scalarMulInitState yst out) (.lit (.number 1))
      (.vals [1] (scalarMulInitState yst out)) := Step.lit
  have hbit : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      scalarMulBodyFuns (scalarMulInitialEnv scalar point out)
      (scalarMulInitState yst out)
      (.builtin .shl [.lit (.number 255), .lit (.number 1)])
      (.vals [scalarMulInitialBit] (scalarMulInitState yst out)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hone) h255) rfl
  simpa [scalarMulLoopEnv, scalarMulInitialBit] using
    (Step.letVal
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := scalarMulBodyFuns)
      (V := scalarMulInitialEnv scalar point out)
      (st := scalarMulInitState yst out)
      (vars := ["\x00151"]) hbit rfl)

theorem step_scalarMulInit (yst : EvmState) (scalar point out : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) yst scalarMulInitBlock
      (scalarMulLoopEnv scalarMulInitialBit scalar point out)
      (scalarMulInitState yst out) .normal := by
  rw [scalarMulInitBlock]
  exact Step.seqCons (step_scalarMulStoreInfinity yst scalar point out)
    (Step.seqCons (step_scalarMulInitialBit yst scalar point out) Step.seqNil)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
