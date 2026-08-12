import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddBody

set_option warningAsError true

/-! Relational call semantics of the frozen G1MSM `fpAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

def fpAddResult (ahi alo bhi blo : U256) : U256 × U256 :=
  let final := fpAddFinalEnv ahi alo bhi blo
  ((VEnv.get final "\x0038").getD (0#256),
   (VEnv.get final "\x0039").getD (0#256))

theorem step_fpAdd_of_args {funs V st argState args} (ahi alo bhi blo : U256)
    (hargs : EvalArgs modexpExec.toDialect funs V st args
      (.vals [ahi, alo, bhi, blo] argState))
    (hlookup : lookupFun funs "\x004" = some (fpAddDecl, sourceFuns)) :
    EvalExpr modexpExec.toDialect funs V st (.call "\x004" args)
      (.vals [(fpAddResult ahi alo bhi blo).1,
        (fpAddResult ahi alo bhi blo).2] argState) := by
  have hbody : ExecStmt modexpExec.toDialect sourceFuns
      (fpAddInitialEnv ahi alo bhi blo) argState (.block fpAddBody)
      (fpAddFinalEnv ahi alo bhi blo) argState .normal := by
    have hseq : ExecStmts modexpExec.toDialect
        (hoist modexpExec.toDialect fpAddBody :: sourceFuns)
        (fpAddInitialEnv ahi alo bhi blo) argState fpAddBody
        (fpAddFinalEnv ahi alo bhi blo) argState .normal := by
      rw [hoist_fpAddBody]
      exact step_fpAddBody ahi alo bhi blo argState
    have h := Step.block (D := modexpExec.toDialect) hseq
    by_cases hc : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
        (fpAddLowValue alo blo) = (0#256)
    · simpa [restore, fpAddInitialEnv, fpAddFinalEnv, hc,
        fpAddHighEnv] using h
    · simpa [restore, fpAddInitialEnv, fpAddFinalEnv, hc,
        fpAddCorrectEnv] using h
  have hcall := Step.callOk hargs hlookup rfl hbody (Or.inl rfl)
  simpa [fpAddDecl, fpAddResult, Dialect.zero, litValue] using hcall

theorem step_fpAdd (ahi alo bhi blo : U256) (yst : EvmState) :
    EvalExpr modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x004" [.var "ahi", .var "alo", .var "bhi", .var "blo"])
      (.vals [(fpAddResult ahi alo bhi blo).1,
        (fpAddResult ahi alo bhi blo).2] yst) := by
  let outer : VEnv modexpExec.toDialect :=
    [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)]
  have hhi : EvalExpr modexpExec.toDialect sourceFuns outer yst
      (.var "ahi") (.vals [ahi] yst) := Step.var rfl
  have halo : EvalExpr modexpExec.toDialect sourceFuns outer yst
      (.var "alo") (.vals [alo] yst) := Step.var rfl
  have hbhi : EvalExpr modexpExec.toDialect sourceFuns outer yst
      (.var "bhi") (.vals [bhi] yst) := Step.var rfl
  have hblo : EvalExpr modexpExec.toDialect sourceFuns outer yst
      (.var "blo") (.vals [blo] yst) := Step.var rfl
  have hargs : EvalArgs modexpExec.toDialect sourceFuns outer yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"]
      (.vals [ahi, alo, bhi, blo] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hblo) hbhi) halo) hhi
  exact step_fpAdd_of_args ahi alo bhi blo hargs lookup_fpAdd

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
