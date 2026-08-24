import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvBody

set_option warningAsError true

/-! # Relational execution contract for frozen G1ADD `fpInv` -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

/-- Relational source-call theorem used by the enclosing G1ADD proof.  Argument
evaluation may change state; the local inversion body preserves the resulting
argument state exactly. -/
theorem step_fpInv_call {callerFuns : FunEnv D} {V : VEnv D}
    {args : List (Expr Op)} {yst argsState : EvmState} (hi lo : U256)
    (hlookup : lookupFun callerFuns "\x0010" = some (fpInvDecl, fpInvFuns))
    (hargs : EvalArgs D callerFuns V yst args (.vals [hi, lo] argsState)) :
    ∃ resultHi resultLo,
      EvalExpr D callerFuns V yst (.call "\x0010" args)
        (.vals [resultHi, resultLo] argsState) ∧
      NativePowResult hi lo resultHi resultLo := by
  obtain ⟨resultHi, resultLo, hbody, hresult⟩ :=
    step_fpInvBody hi lo argsState
  have hcall := Step.callOk hargs hlookup (by rfl) hbody (Or.inl rfl)
  change EvalExpr D callerFuns V yst (.call "\x0010" args)
    (.vals
      [(VEnv.get (fpInvReturnEnv hi lo resultHi resultLo) "\x0082").getD 0,
       (VEnv.get (fpInvReturnEnv hi lo resultHi resultLo) "\x0083").getD 0]
      argsState) at hcall
  rw [fpInvReturnEnv_hi, fpInvReturnEnv_lo] at hcall
  exact ⟨resultHi, resultLo, hcall, hresult⟩

/-- Compatibility spelling for the relational local-call theorem. -/
theorem eval_fpInv {callerFuns : FunEnv D} {V : VEnv D}
    {args : List (Expr Op)} {yst argsState : EvmState} (hi lo : U256)
    (hlookup : lookupFun callerFuns "\x0010" = some (fpInvDecl, fpInvFuns))
    (hargs : EvalArgs D callerFuns V yst args (.vals [hi, lo] argsState)) :
    ∃ resultHi resultLo,
      EvalExpr D callerFuns V yst (.call "\x0010" args)
        (.vals [resultHi, resultLo] argsState) ∧
      NativePowResult hi lo resultHi resultLo :=
  step_fpInv_call hi lo hlookup hargs

/-- The frozen wrapper itself implements the shared implementation-independent
inversion contract and declares no writable memory. -/
theorem fpInv_inversionCorrect :
    YulModexp.InversionCorrect fpInvFuns "\x0010" fpInvDecl
      (fun _ => []) := by
  intro callerFuns V st st1 args request hlookup hargs hpre
  rcases request with ⟨baseHi, baseLo, exponent⟩
  change Fp.Canonical (sourceLimbs baseLo baseHi) ∧
    exponent = Fp.pMinus2Bytes at hpre
  rcases hpre with ⟨hcanonical, rfl⟩
  change EvalArgs _ callerFuns V st args (.vals [baseHi, baseLo] st1) at hargs
  obtain ⟨resultHi, resultLo, heval, hresult⟩ :=
    step_fpInv_call baseHi baseLo hlookup hargs
  refine ⟨[resultHi, resultLo], st1, heval, hresult.refines hcanonical,
    Challenge.YulProof.SoftwareModexp.StateFrame.refl st1,
    Challenge.YulProof.SoftwareModexp.MemoryFrame.refl [] st1⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
