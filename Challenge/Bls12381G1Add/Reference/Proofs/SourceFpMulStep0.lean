import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStart

set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpGeBody : Block Op :=
  match Compilation.referenceCompiledBlock[0]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpGeInitialEnv (hi lo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x0016", hi), ("\x0017", lo), ("\x0018", 0)]

def fpGeResultEnv (hi lo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x0016", hi), ("\x0017", lo), ("\x0018", fpGeModulusValue hi lo)]

theorem lookup_fpGeBody : lookupFun fpReduceBodyFuns "\x000" = some
    ({ params := ["\x0016", "\x0017"]
       rets := ["\x0018"]
       body := fpGeBody }, fpReduceFuns) := by
  rfl

theorem exec_fpGeBody57 (hi lo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 54 fpReduceFuns
      (fpGeInitialEnv hi lo) yst (.block fpGeBody) =
    .ok (fpGeResultEnv hi lo, yst, .normal) := by
  rfl

theorem exec_fpGeBody56 (hi lo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 53 fpReduceFuns
      (fpGeInitialEnv hi lo) yst (.block fpGeBody) =
    .ok (fpGeResultEnv hi lo, yst, .normal) := by
  rfl

theorem eval_fpReduceGe58 (product : FullMulValue)
    (value : FpMulWideValue) (yst : EvmState) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 55 fpReduceBodyFuns
      (fpReduceValueEnv product value) yst
      (.call "\x000" [.var "\x00136", .var "\x00137"]) =
    .ok (.vals [fpGeModulusValue value.hi value.lo] yst) := by
  have hargs : Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 54
      fpReduceBodyFuns (fpReduceValueEnv product value) yst
      [.var "\x00136", .var "\x00137"] =
    .ok (.vals [value.hi, value.lo] yst) := by rfl
  have h := Interp.evalExpr_call_normal hargs lookup_fpGeBody (by rfl)
    (exec_fpGeBody57 value.hi value.lo yst)
  have hout : (VEnv.get (fpGeResultEnv value.hi value.lo) "\x0018").getD 0 =
      fpGeModulusValue value.hi value.lo := by rfl
  change _ = Result.ok (EResult.vals [
    (VEnv.get (fpGeResultEnv value.hi value.lo) "\x0018").getD 0] yst) at h
  rw [hout] at h
  exact h

theorem eval_fpReduceGe57 (product : FullMulValue)
    (value : FpMulWideValue) (yst : EvmState) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 54 fpReduceBodyFuns
      (fpReduceValueEnv product value) yst
      (.call "\x000" [.var "\x00136", .var "\x00137"]) =
    .ok (.vals [fpGeModulusValue value.hi value.lo] yst) := by
  have hargs : Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 53
      fpReduceBodyFuns (fpReduceValueEnv product value) yst
      [.var "\x00136", .var "\x00137"] =
    .ok (.vals [value.hi, value.lo] yst) := by rfl
  have h := Interp.evalExpr_call_normal hargs lookup_fpGeBody (by rfl)
    (exec_fpGeBody56 value.hi value.lo yst)
  have hout : (VEnv.get (fpGeResultEnv value.hi value.lo) "\x0018").getD 0 =
      fpGeModulusValue value.hi value.lo := by rfl
  change _ = Result.ok (EResult.vals [
    (VEnv.get (fpGeResultEnv value.hi value.lo) "\x0018").getD 0] yst) at h
  rw [hout] at h
  exact h

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
