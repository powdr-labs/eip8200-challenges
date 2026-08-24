import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowCorrect

set_option warningAsError true

/-! # Native frozen G1ADD `fpInv` wrapper body -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpInvInitialEnv (hi lo : U256) : VEnv D :=
  [("\x0080", hi), ("\x0081", lo), ("\x0082", 0), ("\x0083", 0)]

def fpInvReturnEnv (hi lo resultHi resultLo : U256) : VEnv D :=
  VEnv.setMany (fpInvInitialEnv hi lo) ["\x0082", "\x0083"]
    [resultHi, resultLo]

def fpInvBodyFuns : FunEnv D := [] :: fpInvFuns

theorem fpInvBody_shape : fpInvBody =
    [.assign ["\x0082", "\x0083"] (.call "\x0013"
      [.var "\x0080", .var "\x0081"])] := by
  rfl

theorem lookup_fpPowPMinus2_fpInvBody :
    lookupFun fpInvBodyFuns "\x0013" =
      some (fpPowPMinus2Decl, fpInvFuns) := by
  rfl

theorem hoist_fpInvBody : hoist D fpInvBody = [] := by
  rw [fpInvBody_shape]
  rfl

theorem restore_fpInvReturnEnv (hi lo resultHi resultLo : U256) :
    restore (fpInvInitialEnv hi lo)
      (fpInvReturnEnv hi lo resultHi resultLo) =
        fpInvReturnEnv hi lo resultHi resultLo := by
  rfl

theorem step_fpInvBody (hi lo : U256) (yst : EvmState) :
    ∃ resultHi resultLo,
      ExecStmt D fpInvFuns (fpInvInitialEnv hi lo) yst (.block fpInvBody)
        (fpInvReturnEnv hi lo resultHi resultLo) yst .normal ∧
      NativePowResult hi lo resultHi resultLo := by
  have hargs : EvalArgs D fpInvBodyFuns (fpInvInitialEnv hi lo) yst
      [.var "\x0080", .var "\x0081"] (.vals [hi, lo] yst) :=
    Step.argsCons (Step.argsCons Step.argsNil (Step.var (by rfl)))
      (Step.var (by rfl))
  obtain ⟨resultHi, resultLo, hcall, hresult⟩ :=
    step_fpPowPMinus2_call hi lo lookup_fpPowPMinus2_fpInvBody hargs
  have hassign : ExecStmt D fpInvBodyFuns (fpInvInitialEnv hi lo) yst
      (.assign ["\x0082", "\x0083"] (.call "\x0013"
        [.var "\x0080", .var "\x0081"]))
      (fpInvReturnEnv hi lo resultHi resultLo) yst .normal :=
    Step.assignVal hcall rfl
  have hseq : ExecStmts D fpInvBodyFuns (fpInvInitialEnv hi lo) yst fpInvBody
      (fpInvReturnEnv hi lo resultHi resultLo) yst .normal := by
    rw [fpInvBody_shape]
    exact Step.seqCons hassign Step.seqNil
  have hseq' : ExecStmts D (hoist D fpInvBody :: fpInvFuns)
      (fpInvInitialEnv hi lo) yst fpInvBody
      (fpInvReturnEnv hi lo resultHi resultLo) yst .normal := by
    simpa [fpInvBodyFuns, hoist_fpInvBody] using hseq
  have hblock := Step.block (funs := fpInvFuns) hseq'
  rw [restore_fpInvReturnEnv] at hblock
  exact ⟨resultHi, resultLo, hblock, hresult⟩

theorem fpInvReturnEnv_hi (hi lo resultHi resultLo : U256) :
    (VEnv.get (fpInvReturnEnv hi lo resultHi resultLo) "\x0082").getD 0 =
      resultHi := by
  rfl

theorem fpInvReturnEnv_lo (hi lo resultHi resultLo : U256) :
    (VEnv.get (fpInvReturnEnv hi lo resultHi resultLo) "\x0083").getD 0 =
      resultLo := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
