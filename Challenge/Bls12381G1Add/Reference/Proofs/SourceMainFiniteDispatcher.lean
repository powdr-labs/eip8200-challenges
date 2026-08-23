import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteMemory
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Complete frozen G1ADD finite dispatcher -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- The complete finite-point source suffix, from the equal-x dispatch through
the canonical return. -/
def mainFiniteDispatcherBody : Block Op :=
  Compilation.referenceCompiledBlock.drop 26

theorem mainFiniteDispatcherBody_eq : mainFiniteDispatcherBody =
    mainFiniteEqualStmt :: mainFiniteUnequalStmt :: mainFinitePostBody := by
  rfl

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).1
    _ _ _ _ _ h

private def finiteXEqCall : Expr Op :=
  .call "\x003"
    [.builtin .mload [.lit (.number 0)],
      .builtin .mload [.lit (.number 32)],
      .builtin .mload [.lit (.number 128)],
      .builtin .mload [.lit (.number 160)]]

private theorem mainFiniteUnequalStmt_shape : mainFiniteUnequalStmt =
    .cond (.builtin .iszero [finiteXEqCall]) mainFiniteUnequalBody := by
  rfl

private theorem finiteXEq_eval (yst st : EvmState)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns base st
      finiteXEqCall
      (.vals [mainFiniteXEqValue yst]
        (afterFourLoads st 0 32 128 160)) := by
  apply sound_evalExpr
  have h := eval_fpEqLoads mainFuns base st 0 32 128 160
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
  rw [hread 0 (by norm_num), hread 32 (by norm_num),
    hread 128 (by norm_num), hread 160 (by norm_num)] at h
  exact h

private theorem step_mainFiniteUnequal_skip (yst st : EvmState)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns base st
      mainFiniteUnequalStmt base (afterFourLoads st 0 32 128 160)
      .normal := by
  rw [mainFiniteUnequalStmt_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      base st (.builtin .iszero [finiteXEqCall])
      (.vals [b2w (mainFiniteXEqValue yst = 0)]
        (afterFourLoads st 0 32 128 160)) :=
    Step.builtinOk
      (Step.argsCons Step.argsNil (finiteXEq_eval yst st base hread)) rfl
  have hzero : b2w (mainFiniteXEqValue yst = 0) =
      Challenge.EvmProof.modexpExec.toDialect.zero := by
    rw [hxeq]
    rfl
  exact Step.ifFalse hcondition hzero

def mainFiniteDoubleResultEnv (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (mainFiniteEnv yst) (mainFiniteDoubleEnv6 yst)

def mainFiniteDoublePostState (yst : EvmState) : EvmState :=
  afterFourLoads (mainFiniteDoubleFinalState yst) 0 32 128 160

private theorem doubleResultEnv_lambdaHi (yst : EvmState) :
    (mainFiniteDoubleResultEnv yst).get "\x0098" =
      some (mainFiniteDoubleLambdaWords yst).1 := by
  rfl

private theorem doubleResultEnv_lambdaLo (yst : EvmState) :
    (mainFiniteDoubleResultEnv yst).get "\x0099" =
      some (mainFiniteDoubleLambdaWords yst).2 := by
  rfl

private theorem unequalResultEnv_lambdaHi (yst : EvmState) :
    (mainFiniteUnequalResultEnv yst).get "\x0098" =
      some (mainFiniteUnequalLambdaWords yst).1 := by
  rfl

private theorem unequalResultEnv_lambdaLo (yst : EvmState) :
    (mainFiniteUnequalResultEnv yst).get "\x0099" =
      some (mainFiniteUnequalLambdaWords yst).2 := by
  rfl

/-- Exact complete finite execution for equal-x nonexceptional doubling. -/
theorem step_mainFiniteDispatcher_double (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst = 0)
    (hx : Fp.Canonical (mainFiniteDoubleX yst))
    (hy : Fp.Canonical (mainFiniteDoubleY yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst)
      mainFiniteDispatcherBody
      (mainFinitePostEnv5 yst (mainFiniteDoubleResultEnv yst)
        (mainFiniteDoublePostState yst) (mainFiniteDoubleLambdaWords yst))
      (mainFinitePostReturnState yst (mainFiniteDoublePostState yst)
        (mainFiniteDoubleLambdaWords yst)) .halt := by
  rw [mainFiniteDispatcherBody_eq]
  have hequal := step_mainFiniteEqual_nonexceptional yst hxeq hyeq hyzero
    (step_mainFiniteDoubleBody_canonical yst hx hy)
  have hskip := step_mainFiniteUnequal_skip yst
    (mainFiniteDoubleFinalState yst) (mainFiniteDoubleResultEnv yst) hxeq
    (mainFiniteDoubleFinalState_loadWord yst)
  have hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord (mainFiniteDoublePostState yst).memory offset =
        mainDecodedWord yst offset := by
    intro offset hend
    rw [mainFiniteDoublePostState, afterFourLoads_memory]
    exact mainFiniteDoubleFinalState_loadWord yst offset hend
  exact Step.seqCons hequal (Step.seqCons hskip
    (step_mainFinitePostBody yst (mainFiniteDoublePostState yst)
      (mainFiniteDoubleLambdaWords yst) (mainFiniteDoubleResultEnv yst)
      (doubleResultEnv_lambdaHi yst) (doubleResultEnv_lambdaLo yst) hread))

/-- Exact complete finite execution for unequal x-coordinates. -/
theorem step_mainFiniteDispatcher_unequal (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 0)
    (hx1 : Fp.Canonical (mainFiniteUnequalX1 yst))
    (hx2 : Fp.Canonical (mainFiniteUnequalX2 yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst)
      mainFiniteDispatcherBody
      (mainFinitePostEnv5 yst (mainFiniteUnequalResultEnv yst)
        (mainFiniteUnequalFinalState yst) (mainFiniteUnequalLambdaWords yst))
      (mainFinitePostReturnState yst (mainFiniteUnequalFinalState yst)
        (mainFiniteUnequalLambdaWords yst)) .halt := by
  rw [mainFiniteDispatcherBody_eq]
  exact Step.seqCons (step_mainFiniteEqual_skip yst hxeq)
    (Step.seqCons (step_mainFiniteUnequal_canonical yst hxeq hx1 hx2)
      (step_mainFinitePostBody yst (mainFiniteUnequalFinalState yst)
        (mainFiniteUnequalLambdaWords yst) (mainFiniteUnequalResultEnv yst)
        (unequalResultEnv_lambdaHi yst) (unequalResultEnv_lambdaLo yst)
        (mainFiniteUnequalFinalState_loadWord yst)))

/-- Equal-x opposite points halt before slope arithmetic and return infinity. -/
theorem step_mainFiniteDispatcher_opposite (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst)
      mainFiniteDispatcherBody (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt := by
  rw [mainFiniteDispatcherBody_eq]
  exact Step.seqStop (step_mainFiniteEqual_opposite yst hxeq hyeq) (by decide)

/-- Equal-point `y=0` halts before slope arithmetic and returns infinity. -/
theorem step_mainFiniteDispatcher_zeroY (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst)
      mainFiniteDispatcherBody (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt := by
  rw [mainFiniteDispatcherBody_eq]
  exact Step.seqStop (step_mainFiniteEqual_zeroY yst hxeq hyeq hyzero)
    (by decide)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
