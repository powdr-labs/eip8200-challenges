import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvCall

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_montMul2_nativeResult
    {callerFuns : FunEnv Challenge.YulProof.ClosedEvm.dialect}
    {V : VEnv Challenge.YulProof.ClosedEvm.dialect} {args : List (Expr Op)}
    {yst : EvmState} (xLo xHi yLo yHi : U256)
    (hlookup : lookupFun callerFuns "\x0015" = some (montMul2Decl, fpInvFuns))
    (hargs : EvalArgs Challenge.YulProof.ClosedEvm.dialect callerFuns V yst args
      (.vals [xLo, xHi, yLo, yHi] yst)) :
    ∃ zLo zHi,
      EvalExpr Challenge.YulProof.ClosedEvm.dialect callerFuns V yst
        (.call "\x0015" args) (.vals [zLo, zHi] yst) ∧
      NativeMontMulResult xLo xHi yLo yHi zLo zHi := by
  refine ⟨(montMul2Value xLo xHi yLo yHi).lo,
    (montMul2Value xLo xHi yLo yHi).hi,
    step_montMul2_call xLo xHi yLo yHi hlookup hargs, ?_⟩
  simp only [NativeMontMulResult]
  exact ⟨True.intro, True.intro⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
