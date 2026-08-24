import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMontCorrectionBody
import Challenge.YulProof.Interpreter

set_option warningAsError true

/-! # Native frozen G1ADD `montMul2` execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.YulProof.Interpreter

def montMul2BranchFinalEnv (xLo xHi yLo yHi : U256) :
    VEnv Challenge.YulProof.ClosedEvm.dialect :=
  if fpGeModulusValue (montSecond xLo xHi yLo yHi).t1
      (montSecond xLo xHi yLo yHi).t0 = 0 then
    correctionEnv0 xLo xHi yLo yHi
  else
    restore (correctionEnv0 xLo xHi yLo yHi)
      (correctionEnv5 xLo xHi yLo yHi)

private theorem execStmts_append_normal {funs : FunEnv Challenge.YulProof.ClosedEvm.dialect}
    {V V1 V2 : VEnv Challenge.YulProof.ClosedEvm.dialect}
    {yst yst1 yst2 : EvmState} {xs ys : List (Stmt Op)} {outcome : Outcome}
    (hxs : ExecStmts Challenge.YulProof.ClosedEvm.dialect funs V yst xs V1 yst1 .normal)
    (hys : ExecStmts Challenge.YulProof.ClosedEvm.dialect funs V1 yst1 ys V2 yst2 outcome) :
    ExecStmts Challenge.YulProof.ClosedEvm.dialect funs V yst (xs ++ ys) V2 yst2 outcome := by
  induction xs generalizing V yst with
  | nil =>
      cases hxs
      simpa using hys
  | cons _ _ ih =>
      cases hxs with
      | seqCons hs hrest => exact Step.seqCons hs (ih hrest)
      | seqStop _ hne => exact (hne rfl).elim

theorem step_montMul2_correction (xLo xHi yLo yHi : U256)
    (yst : EvmState) :
    ExecStmt Challenge.YulProof.ClosedEvm.dialect montMul2BodyFuns
      (montMul2OutputEnv (montMul2InitialEnv xLo xHi yLo yHi)
        (montAccumulated xLo xHi yLo yHi) (montSecond xLo xHi yLo yHi)) yst
      montMul2Stmt9 (montMul2BranchFinalEnv xLo xHi yLo yHi) yst .normal := by
  rw [montMul2Stmt9_shape]
  rw [← correctionEnv0]
  by_cases hzero : fpGeModulusValue (montSecond xLo xHi yLo yHi).t1
      (montSecond xLo xHi yLo yHi).t0 = 0
  · rw [montMul2BranchFinalEnv, if_pos hzero]
    exact Step.ifFalse (eval_montMul2CorrectionCondition xLo xHi yLo yHi yst) hzero
  · rw [montMul2BranchFinalEnv, if_neg hzero]
    exact Step.ifTrue
      (eval_montMul2CorrectionCondition xLo xHi yLo yHi yst) hzero
      (exec_montMul2CorrectionBody xLo xHi yLo yHi yst)

theorem step_montMul2Body (xLo xHi yLo yHi : U256) (yst : EvmState) :
    ExecStmt Challenge.YulProof.ClosedEvm.dialect fpInvFuns
      (montMul2InitialEnv xLo xHi yLo yHi) yst (.block montMul2Body)
      (restore (montMul2InitialEnv xLo xHi yLo yHi)
        (montMul2BranchFinalEnv xLo xHi yLo yHi)) yst .normal := by
  have h03 := execStmts_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (interp_montMul2_prefix xLo xHi yLo yHi yst)
  have h45 := execStmts_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (interp_montMul2_firstReduce xLo xHi yLo yHi yst)
  have h6 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (interp_montMul2_accumulate xLo xHi yLo yHi yst)
  have h7 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (interp_montMul2_secondFactor xLo xHi yLo yHi yst)
  have h8 := execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
    (interp_montMul2_secondReduce xLo xHi yLo yHi yst)
  have hstmts := execStmts_append_normal h03 (execStmts_append_normal h45
    (Step.seqCons h6 (Step.seqCons h7
      (Step.seqCons h8 (Step.seqCons
        (step_montMul2_correction xLo xHi yLo yHi yst) Step.seqNil)))))
  change ExecStmts Challenge.YulProof.ClosedEvm.dialect montMul2BodyFuns
    (montMul2InitialEnv xLo xHi yLo yHi) yst
    [montMul2Stmt0, montMul2Stmt1, montMul2Stmt2, montMul2Stmt3,
      montMul2Stmt4, montMul2Stmt5, montMul2Stmt6, montMul2Stmt7,
      montMul2Stmt8, montMul2Stmt9]
    (montMul2BranchFinalEnv xLo xHi yLo yHi) yst .normal at hstmts
  rw [← montMul2Body_eq] at hstmts
  have hfuns : montMul2BodyFuns =
      hoist Challenge.YulProof.ClosedEvm.dialect montMul2Body :: fpInvFuns := by
    rfl
  rw [hfuns] at hstmts
  exact Step.block (D := Challenge.YulProof.ClosedEvm.dialect) hstmts

theorem montMul2BodyResult_lo (xLo xHi yLo yHi : U256) :
    (VEnv.get
      (restore (montMul2InitialEnv xLo xHi yLo yHi)
        (montMul2BranchFinalEnv xLo xHi yLo yHi)) "\x00170").getD 0 =
      (montMul2Value xLo xHi yLo yHi).lo := by
  rw [montMul2Value_eq_stages]
  by_cases hzero : fpGeModulusValue (montSecond xLo xHi yLo yHi).t1
      (montSecond xLo xHi yLo yHi).t0 = 0
  · simp only [montMul2BranchFinalEnv, correctionEnv0,
      montMul2OutputEnv, montMul2FactorEnv, montMul2WorkEnv,
      montMul2StateEnv, montMul2InitialEnv, montFinalCorrectValue, hzero]
    rfl
  · simp only [montMul2BranchFinalEnv, correctionEnv5,
      correctionEnv4, correctionEnv3, correctionEnv2, correctionEnv1,
      correctionEnv0, montMul2OutputEnv, montMul2FactorEnv, montMul2WorkEnv,
      montMul2StateEnv, montMul2InitialEnv, montFinalCorrectValue, hzero]
    rfl

theorem montMul2BodyResult_hi (xLo xHi yLo yHi : U256) :
    (VEnv.get
      (restore (montMul2InitialEnv xLo xHi yLo yHi)
        (montMul2BranchFinalEnv xLo xHi yLo yHi)) "\x00171").getD 0 =
      (montMul2Value xLo xHi yLo yHi).hi := by
  rw [montMul2Value_eq_stages]
  by_cases hzero : fpGeModulusValue (montSecond xLo xHi yLo yHi).t1
      (montSecond xLo xHi yLo yHi).t0 = 0
  · simp only [montMul2BranchFinalEnv, correctionEnv0,
      montMul2OutputEnv, montMul2FactorEnv, montMul2WorkEnv,
      montMul2StateEnv, montMul2InitialEnv, montFinalCorrectValue, hzero]
    rfl
  · simp only [montMul2BranchFinalEnv, correctionEnv5,
      correctionEnv4, correctionEnv3, correctionEnv2, correctionEnv1,
      correctionEnv0, montMul2OutputEnv, montMul2FactorEnv, montMul2WorkEnv,
      montMul2StateEnv, montMul2InitialEnv, montFinalCorrectValue, hzero]
    rfl

theorem step_montMul2_call {callerFuns : FunEnv Challenge.YulProof.ClosedEvm.dialect}
    {V : VEnv Challenge.YulProof.ClosedEvm.dialect} {args : List (Expr Op)}
    {yst : EvmState} (xLo xHi yLo yHi : U256)
    (hlookup : lookupFun callerFuns "\x0015" = some (montMul2Decl, fpInvFuns))
    (hargs : EvalArgs Challenge.YulProof.ClosedEvm.dialect callerFuns V yst args
      (.vals [xLo, xHi, yLo, yHi] yst)) :
    EvalExpr Challenge.YulProof.ClosedEvm.dialect callerFuns V yst
      (.call "\x0015" args)
      (.vals [(montMul2Value xLo xHi yLo yHi).lo,
        (montMul2Value xLo xHi yLo yHi).hi] yst) := by
  have hcall := Step.callOk hargs hlookup (by rfl)
    (step_montMul2Body xLo xHi yLo yHi yst) (Or.inl rfl)
  change EvalExpr Challenge.YulProof.ClosedEvm.dialect callerFuns V yst
    (.call "\x0015" args)
    (.vals
      [(VEnv.get (restore (montMul2InitialEnv xLo xHi yLo yHi)
          (montMul2BranchFinalEnv xLo xHi yLo yHi)) "\x00170").getD 0,
       (VEnv.get (restore (montMul2InitialEnv xLo xHi yLo yHi)
          (montMul2BranchFinalEnv xLo xHi yLo yHi)) "\x00171").getD 0] yst) at hcall
  rw [montMul2BodyResult_lo, montMul2BodyResult_hi] at hcall
  exact hcall

set_option linter.defProp false in
@[irreducible] def NativeMontMulResult (xLo xHi yLo yHi zLo zHi : U256) : Prop :=
  ∀ (_hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
        { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi })
      (_hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }),
    Challenge.Bls12381.ProofSupport.Fp.Canonical
        { lo := YulEvmCompiler.conv zLo, hi := YulEvmCompiler.conv zHi } ∧
      (Challenge.Bls12381.ProofSupport.Fp.value
          { lo := YulEvmCompiler.conv zLo, hi := YulEvmCompiler.conv zHi } :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) =
        (Challenge.Bls12381.ProofSupport.Fp.value
          { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi } :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) *
        (Challenge.Bls12381.ProofSupport.Fp.value
          { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) *
        (Challenge.Bls12381.ProofSupport.Fp.montgomeryRadix :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp)⁻¹

theorem NativeMontMulResult.spec {xLo xHi yLo yHi zLo zHi : U256}
    (hresult : NativeMontMulResult xLo xHi yLo yHi zLo zHi)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi })
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
        { lo := YulEvmCompiler.conv zLo, hi := YulEvmCompiler.conv zHi } ∧
      (Challenge.Bls12381.ProofSupport.Fp.value
          { lo := YulEvmCompiler.conv zLo, hi := YulEvmCompiler.conv zHi } :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) =
        (Challenge.Bls12381.ProofSupport.Fp.value
          { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi } :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) *
        (Challenge.Bls12381.ProofSupport.Fp.value
          { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) *
        (Challenge.Bls12381.ProofSupport.Fp.montgomeryRadix :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp)⁻¹ := by
  unfold NativeMontMulResult at hresult
  exact hresult hx hy

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
