import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowBody

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

theorem step_fpPowPMinus2_call {callerFuns : FunEnv D} {V : VEnv D}
    {args : List (Expr Op)} {yst : EvmState} (aHi aLo : U256)
    (hlookup : lookupFun callerFuns "\x0013" = some (fpPowPMinus2Decl, fpInvFuns))
    (hargs : EvalArgs D callerFuns V yst args (.vals [aHi, aLo] yst)) :
    ∃ resultHi resultLo,
      EvalExpr D callerFuns V yst (.call "\x0013" args)
        (.vals [resultHi, resultLo] yst) ∧
      NativePowResult aHi aLo resultHi resultLo := by
  obtain ⟨resultHi, resultLo, hbody, hresult⟩ :=
    step_fpPowBody aHi aLo yst
  have hcall := Step.callOk hargs hlookup (by rfl) hbody (Or.inl rfl)
  change EvalExpr D callerFuns V yst (.call "\x0013" args)
    (.vals
      [(VEnv.get (fpPowReturnEnv aHi aLo
        { lo := resultLo, hi := resultHi }) "\x00125").getD 0,
       (VEnv.get (fpPowReturnEnv aHi aLo
        { lo := resultLo, hi := resultHi }) "\x00126").getD 0] yst) at hcall
  rw [fpPowReturnEnv_hi, fpPowReturnEnv_lo] at hcall
  exact ⟨resultHi, resultLo, hcall, hresult⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
