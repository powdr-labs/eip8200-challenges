import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulExec
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Constant stores in frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs
      V st stmts V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

theorem exec_onCurveConstantStores (yst : EvmState) (x y : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv x y) (onCurveStateAfterX3 yst x y)
      [onCurveStmt3, onCurveStmt4, onCurveStmt5, onCurveStmt6]
      (onCurveInitialEnv x y) (onCurveStateAfterConstant yst x y) .normal := by
  exact soundStmts (n := 16) (by rfl)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
