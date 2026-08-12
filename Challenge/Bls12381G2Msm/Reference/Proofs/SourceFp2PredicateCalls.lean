import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2Predicates
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Relational call boundaries for the frozen G2MSM Fp2 predicates. -/

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

def fp2ZeroInitialEnv (ptr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00101", ptr), ("\x00102", 0)]

def fp2ZeroFinalEnv (yst : EvmState) (ptr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (fp2ZeroInitialEnv ptr) "\x00102" (fp2ZeroValue yst ptr)

private theorem exec_fp2ZeroBody (ptr : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fp2Funs
      (fp2ZeroInitialEnv ptr) yst (.block fp2ZeroBody) =
    .ok (fp2ZeroFinalEnv yst ptr, fp2ReadState yst ptr, .normal) := by rfl

theorem step_fp2Zero_of_args {funs V st argState args} (ptr : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [ptr] argState))
    (hlookup : lookupFun funs "\x0012" = some (fp2ZeroDecl, fp2Funs)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0012" args)
      (.vals [fp2ZeroValue argState ptr] (fp2ReadState argState ptr)) := by
  have hbody := soundStmt (exec_fp2ZeroBody ptr argState)
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [fp2ZeroDecl, fp2ZeroInitialEnv, fp2ZeroFinalEnv,
    VEnv.get, VEnv.set] using hcall

def fp2EqInitialEnv (a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00103", a), ("\x00104", b), ("\x00105", 0)]

def fp2EqFinalEnv (yst : EvmState) (a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (fp2EqInitialEnv a b) "\x00105" (fp2EqValue yst a b)

private theorem exec_fp2EqBody (a b : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fp2Funs
      (fp2EqInitialEnv a b) yst (.block fp2EqBody) =
    .ok (fp2EqFinalEnv yst a b, fp2EqReadState yst a b, .normal) := by rfl

theorem step_fp2Eq_of_args {funs V st argState args} (a b : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [a, b] argState))
    (hlookup : lookupFun funs "\x0013" = some (fp2EqDecl, fp2Funs)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0013" args)
      (.vals [fp2EqValue argState a b] (fp2EqReadState argState a b)) := by
  have hbody := soundStmt (exec_fp2EqBody a b argState)
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [fp2EqDecl, fp2EqInitialEnv, fp2EqFinalEnv,
    VEnv.get, VEnv.set] using hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
