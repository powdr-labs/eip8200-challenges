import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowRefinement

set_option warningAsError true

/-! # Implementation-independent contract for native source exponentiation -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- The frozen `fpPowPMinus2` declaration implements fixed-exponent inversion
without touching EVM state or memory. -/
theorem fpPowPMinus2_inversionCorrect :
    YulModexp.InversionCorrect fpInvFuns "\x0013" fpPowPMinus2Decl
      (fun _ => []) := by
  intro callerFuns V st st1 args request hlookup hargs hpre
  rcases request with ⟨baseHi, baseLo, exponent⟩
  change Fp.Canonical (sourceLimbs baseLo baseHi) ∧
    exponent = Fp.pMinus2Bytes at hpre
  rcases hpre with ⟨hcanonical, rfl⟩
  change EvalArgs _ callerFuns V st args (.vals [baseHi, baseLo] st1) at hargs
  obtain ⟨resultHi, resultLo, heval, hresult⟩ :=
    step_fpPowPMinus2_call baseHi baseLo hlookup hargs
  refine ⟨[resultHi, resultLo], st1, heval, ?_,
    Challenge.YulProof.SoftwareModexp.StateFrame.refl st1,
    Challenge.YulProof.SoftwareModexp.MemoryFrame.refl [] st1⟩
  exact hresult.refines hcanonical

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
