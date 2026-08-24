import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvResultDefs

set_option warningAsError true

/-! # Canonical bridge from native execution words to the stable result -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

/-- Canonical arithmetic refinement identifies every operational result with
the stable public result words.  This proof passes through the auditor-facing
`YulModexp.Refines` contract and does not expose Montgomery internals. -/
theorem NativePowResult.eq_fpInvResult {yst : EvmState}
    {hi lo resultHi resultLo : U256}
    (hresult : NativePowResult hi lo resultHi resultLo)
    (hcanonical : Fp.Canonical (fpInvInputLimbs hi lo)) :
    (resultHi, resultLo) = fpInvResult yst hi lo := by
  have hrefines := hresult.refines (by
    simpa [sourceLimbs, fpInvInputLimbs] using hcanonical)
  obtain ⟨outHi, outLo, hwords, hlimbs⟩ :=
    hrefines.pMinus2_eq_invCanonical hcanonical
  injection hwords with houtHi htail
  injection htail with houtLo
  subst resultHi
  subst resultLo
  apply Prod.ext
  · apply YulEvmCompiler.conv_injective
    rw [fpInvResult_hi_conv]
    exact congrArg Fp.Limbs.hi hlimbs
  · apply YulEvmCompiler.conv_injective
    rw [fpInvResult_lo_conv]
    exact congrArg Fp.Limbs.lo hlimbs

/-- Canonical source calls return the stable public inversion words exactly. -/
theorem step_fpInv_call_result {callerFuns : FunEnv D} {V : VEnv D}
    {args : List (Expr Op)} {yst argsState : EvmState} (hi lo : U256)
    (hlookup : lookupFun callerFuns "\x0010" = some (fpInvDecl, fpInvFuns))
    (hargs : EvalArgs D callerFuns V yst args (.vals [hi, lo] argsState))
    (hcanonical : Fp.Canonical (fpInvInputLimbs hi lo)) :
    EvalExpr D callerFuns V yst (.call "\x0010" args)
      (.vals [(fpInvResult argsState hi lo).1,
        (fpInvResult argsState hi lo).2] argsState) ∧
    YulModexp.Refines (YulModexp.inversionRequest hi lo)
      [(fpInvResult argsState hi lo).1,
        (fpInvResult argsState hi lo).2] := by
  obtain ⟨resultHi, resultLo, heval, hresult⟩ :=
    step_fpInv_call hi lo hlookup hargs
  have hwords := hresult.eq_fpInvResult (yst := argsState) hcanonical
  have hhi := congrArg Prod.fst hwords
  have hlo := congrArg Prod.snd hwords
  change resultHi = (fpInvResult argsState hi lo).1 at hhi
  change resultLo = (fpInvResult argsState hi lo).2 at hlo
  rw [hhi, hlo] at heval
  refine ⟨heval, ?_⟩
  simpa [hhi, hlo] using hresult.refines (by
    simpa [sourceLimbs, fpInvInputLimbs] using hcanonical)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
