import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteClassify
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubExec

set_option warningAsError true

/-! # Literal-pointer Fp2 call boundaries for frozen G2ADD main -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).1
    _ _ _ _ _ h

theorem step_fp2AddLiteral (V) (yst : EvmState) (out a b : Nat) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.call "\x0014" [.lit (.number out), .lit (.number a), .lit (.number b)])
      (.vals [] (fp2AddContractState yst out a b)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 71 mainFuns V yst
      [.lit (.number out), .lit (.number a), .lit (.number b)] =
      Interp.evalArgs Challenge.EvmProof.modexpExec 71 fp2AddFuns
        [("out", BitVec.ofNat 256 out), ("a", BitVec.ofNat 256 a),
          ("b", BitVec.ofNat 256 b)] yst [.var "out", .var "a", .var "b"] := by
    rfl
  have h : Interp.evalExpr Challenge.EvmProof.modexpExec 72 mainFuns V yst
      (.call "\x0014" [.lit (.number out), .lit (.number a), .lit (.number b)]) =
      .ok (.vals [] (fp2AddContractState yst out a b)) := by
    rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
      (fn := "\x0014") hargs (by rfl)]
    exact eval_fp2AddContractState _ _ _ _
  exact sound_evalExpr h

theorem step_fp2SubLiteral (V) (yst : EvmState) (out a b : Nat) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.call "\x0015" [.lit (.number out), .lit (.number a), .lit (.number b)])
      (.vals [] (fp2SubFinalState yst out a b)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 71 mainFuns V yst
      [.lit (.number out), .lit (.number a), .lit (.number b)] =
      Interp.evalArgs Challenge.EvmProof.modexpExec 71 fp2SubFuns
        [("out", BitVec.ofNat 256 out), ("a", BitVec.ofNat 256 a),
          ("b", BitVec.ofNat 256 b)] yst [.var "out", .var "a", .var "b"] := by
    rfl
  have h : Interp.evalExpr Challenge.EvmProof.modexpExec 72 mainFuns V yst
      (.call "\x0015" [.lit (.number out), .lit (.number a), .lit (.number b)]) =
      .ok (.vals [] (fp2SubFinalState yst out a b)) := by
    rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
      (fn := "\x0015") hargs (by rfl)]
    exact eval_fp2Sub _ _ _ _
  exact sound_evalExpr h

theorem step_fp2MulLiteral (V) (yst : EvmState) (out a b : Nat) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.call "\x0016" [.lit (.number out), .lit (.number a), .lit (.number b)])
      (.vals [] (fp2MulFinalState yst out a b)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      [.lit (.number out), .lit (.number a), .lit (.number b)]
      (.vals [out, a, b] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
      Step.lit
  have hcall := Step.callOk hargs
    (show lookupFun mainFuns "\x0016" = some (fp2MulDecl, mainFuns) by rfl)
    (by rfl) (step_fp2MulBody yst out a b) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
    (.call "\x0016" [.lit (.number out), .lit (.number a), .lit (.number b)])
    (.vals (fp2MulDecl.rets.map (fun r =>
      (VEnv.get (fp2MulBodyResultEnv yst out a b) r).getD 0))
      (fp2MulFinalState yst out a b)) at hcall
  simpa [fp2MulDecl] using hcall

theorem step_fp2InvLiteral (V) (yst : EvmState) (out a : Nat)
    (hhi : (fp2InvNorm yst a).1.toNat < 2 ^ 128) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.call "\x0017" [.lit (.number out), .lit (.number a)])
      (.vals [] (fp2InvFinalState yst out a)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      [.lit (.number out), .lit (.number a)] (.vals [out, a] yst) :=
    Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  have hcall := Step.callOk hargs
    (show lookupFun mainFuns "\x0017" = some (fp2InvDecl, mainFuns) by rfl)
    (by rfl) (step_fp2InvBody yst out a hhi) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
    (.call "\x0017" [.lit (.number out), .lit (.number a)])
    (.vals (fp2InvDecl.rets.map (fun r =>
      (VEnv.get (fp2InvBodyResultEnv yst out a) r).getD 0))
      (fp2InvFinalState yst out a)) at hcall
  simpa [fp2InvDecl] using hcall

theorem step_fp2EqLiteral (V) (yst : EvmState) (a b : Nat) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.call "\x0013" [.lit (.number a), .lit (.number b)])
      (.vals [fp2EqValue yst a b] (fp2EqReadState yst a b)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns V yst
      [.lit (.number a), .lit (.number b)] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
      [("a", BitVec.ofNat 256 a), ("b", BitVec.ofNat 256 b)] yst
      [.var "a", .var "b"] := by rfl
  have h : Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns V yst
      (.call "\x0013" [.lit (.number a), .lit (.number b)]) =
      .ok (.vals [fp2EqValue yst a b] (fp2EqReadState yst a b)) := by
    rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
      (fn := "\x0013") hargs (by rfl)]
    exact eval_fp2Eq _ _ _
  exact sound_evalExpr h

theorem step_fp2ZeroLiteral (V) (yst : EvmState) (a : Nat) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns V yst
      (.call "\x0012" [.lit (.number a)])
      (.vals [fp2ZeroValue yst a] (fp2ReadState yst a)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 67 mainFuns V yst
      [.lit (.number a)] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 67 fp2Funs
      [("a", BitVec.ofNat 256 a)] yst [.var "a"] := by rfl
  have h : Interp.evalExpr Challenge.EvmProof.modexpExec 68 mainFuns V yst
      (.call "\x0012" [.lit (.number a)]) =
      .ok (.vals [fp2ZeroValue yst a] (fp2ReadState yst a)) := by
    rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
      (fn := "\x0012") hargs (by rfl)]
    exact eval_fp2Zero _ _
  exact sound_evalExpr h

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
