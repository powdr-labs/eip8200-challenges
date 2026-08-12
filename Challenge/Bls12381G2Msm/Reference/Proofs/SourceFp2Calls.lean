import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AddExec
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2SubExec
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2MulExec
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvExec
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Relational call transport for frozen G2MSM Fp2 arithmetic helpers. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

theorem step_fp2Add_of_args {funs V st argState args} (out a b : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [out, a, b] argState))
    (hlookup : lookupFun funs "\x0014" = some (fp2AddDecl, fp2AddFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0014" args) (.vals [] (fp2AddFinalState argState out a b)) := by
  have hbody := soundStmt (exec_fp2AddBody argState out a b)
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [fp2AddDecl] using hcall

theorem step_fp2Sub_of_args {funs V st argState args} (out a b : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [out, a, b] argState))
    (hlookup : lookupFun funs "\x0015" = some (fp2SubDecl, fp2SubFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0015" args) (.vals [] (fp2SubFinalState argState out a b)) := by
  have hbody := soundStmt (exec_fp2SubBody argState out a b)
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [fp2SubDecl] using hcall

theorem step_fp2Mul_of_args {funs V st argState args} (out a b : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [out, a, b] argState))
    (hlookup : lookupFun funs "\x0016" = some (fp2MulDecl, fp2MulFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0016" args) (.vals [] (fp2MulFinalState argState out a b)) := by
  have hcall := Step.callOk hargs hlookup rfl
    (step_fp2MulBody argState out a b) (Or.inl rfl)
  simpa [fp2MulDecl] using hcall

theorem step_fp2Inv_of_args {funs V st argState args} (out a : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [out, a] argState))
    (hlookup : lookupFun funs "\x0017" = some (fp2InvDecl, fp2InvFuns))
    (hhi : (fp2InvNorm argState a).1.toNat < 2 ^ 128) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0017" args) (.vals [] (fp2InvFinalState argState out a)) := by
  have hcall := Step.callOk hargs hlookup rfl
    (step_fp2InvBody argState out a hhi) (Or.inl rfl)
  simpa [fp2InvDecl] using hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
