import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteClassify

set_option warningAsError true

/-! # G1ADD finite vertical-tangent execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- Environment after the source's two-word slope declaration. -/
def mainFiniteEnv (_yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["\x0098", "\x0099"]

/-- State after evaluating the equal-x dispatch's four loads. -/
def mainFiniteXEqArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainValidatedState yst) 0 32 128 160

/-- State after evaluating the opposite-point test's four y loads. -/
def mainFiniteYEqArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainFiniteXEqArgsState yst) 64 96 192 224

def afterTwoLoads (yst : EvmState) (hiOffset loOffset : Nat) :
    EvmState := touchMemory (touchMemory yst loOffset 32) hiOffset 32

/-- Exact source zero test used by the equal-point `y = 0` branch. -/
def mainFiniteYZeroValue (yst : EvmState) : U256 :=
  fpZeroValue (mainDecodedWord yst 64) (mainDecodedWord yst 96)

/-- State after evaluating the equal-point zero-y test. -/
def mainFiniteYZeroArgsState (yst : EvmState) : EvmState :=
  afterTwoLoads (mainFiniteYEqArgsState yst) 64 96

private def finiteInfinityStoredState (yst : EvmState) : EvmState :=
  mainStorePointState yst 0 0 0 0

private def finiteInfinityReturnState (yst : EvmState) : EvmState :=
  { touchMemory (finiteInfinityStoredState yst) 0 128 with
    halted := some (.ret, readBytes (finiteInfinityStoredState yst).memory 0 128) }

/-- Exact halted state of the corrected opposite-point branch. -/
def mainFiniteOppositeReturnState (yst : EvmState) : EvmState :=
  finiteInfinityReturnState (mainFiniteYEqArgsState yst)

/-- Exact halted state of the corrected equal-point/y-zero branch. -/
def mainFiniteZeroYReturnState (yst : EvmState) : EvmState :=
  finiteInfinityReturnState (mainFiniteYZeroArgsState yst)

private def fpEqLoads (aHi aLo bHi bLo : Nat) : Expr Op :=
  .call "\x003"
    [.builtin .mload [.lit (.number aHi)],
      .builtin .mload [.lit (.number aLo)],
      .builtin .mload [.lit (.number bHi)],
      .builtin .mload [.lit (.number bLo)]]

private def fpZeroLoads (hi lo : Nat) : Expr Op :=
  .call "\x002"
    [.builtin .mload [.lit (.number hi)],
      .builtin .mload [.lit (.number lo)]]

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] theorem afterFourLoads_memory (yst : EvmState)
    (xHi xLo yHi yLo : Nat) :
    (afterFourLoads yst xHi xLo yHi yLo).memory = yst.memory := rfl

@[simp] theorem afterTwoLoads_memory (yst : EvmState)
    (hi lo : Nat) : (afterTwoLoads yst hi lo).memory = yst.memory := rfl

/-- The finite exceptional tests only read memory, so every decoded word is
preserved for the arithmetic branch that follows them. -/
theorem mainFiniteYZeroArgsState_loadWord (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteYZeroArgsState yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteYZeroArgsState, afterTwoLoads_memory,
    mainFiniteYEqArgsState, afterFourLoads_memory,
    mainFiniteXEqArgsState, afterFourLoads_memory]
  exact mainValidatedState_loadWord yst offset hend

theorem eval_fpEqLoads
    (funs : FunEnv Challenge.EvmProof.modexpExec.toDialect)
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (aHi aLo bHi bLo : Nat)
    (haHi : aHi < 2 ^ 256) (haLo : aLo < 2 ^ 256)
    (hbHi : bHi < 2 ^ 256) (hbLo : bLo < 2 ^ 256)
    (hlookup : lookupFun funs "\x003" = lookupFun mainFuns "\x003") :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 funs V yst
      (fpEqLoads aHi aLo bHi bLo) =
      .ok (.vals
        [fpEqValue (loadWord yst.memory aHi) (loadWord yst.memory aLo)
          (loadWord yst.memory bHi) (loadWord yst.memory bLo)]
        (afterFourLoads yst aHi aLo bHi bLo)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 64 funs V yst
          [.builtin .mload [.lit (.number aHi)],
            .builtin .mload [.lit (.number aLo)],
            .builtin .mload [.lit (.number bHi)],
            .builtin .mload [.lit (.number bLo)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
          [("ahi", loadWord yst.memory aHi),
            ("alo", loadWord yst.memory aLo),
            ("bhi", loadWord yst.memory bHi),
            ("blo", loadWord yst.memory bLo)]
          (afterFourLoads yst aHi aLo bHi bLo)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    norm_num at haHi haLo hbHi hbLo
    simp [Interp.evalArgs, Interp.evalExpr, afterFourLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt haHi,
      Nat.mod_eq_of_lt haLo, Nat.mod_eq_of_lt hbHi,
      Nat.mod_eq_of_lt hbLo, VEnv.get]
  rw [fpEqLoads,
    Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x003") hargs hlookup]
  exact eval_fpEq _ _ _ _ _

private theorem eval_fpZeroLoads
    (funs : FunEnv Challenge.EvmProof.modexpExec.toDialect)
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (hi lo : Nat) (hhi : hi < 2 ^ 256) (hlo : lo < 2 ^ 256)
    (hlookup : lookupFun funs "\x002" = lookupFun mainFuns "\x002") :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 funs V yst
      (fpZeroLoads hi lo) =
      .ok (.vals
        [fpZeroValue (loadWord yst.memory hi) (loadWord yst.memory lo)]
        (afterTwoLoads yst hi lo)) := by
  have hargs :
      Interp.evalArgs Challenge.EvmProof.modexpExec 64 funs V yst
          [.builtin .mload [.lit (.number hi)],
            .builtin .mload [.lit (.number lo)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
          [("hi", loadWord yst.memory hi), ("lo", loadWord yst.memory lo)]
          (afterTwoLoads yst hi lo) [.var "hi", .var "lo"] := by
    norm_num at hhi hlo
    simp [Interp.evalArgs, Interp.evalExpr, afterTwoLoads,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, EVM.litValue, Nat.mod_eq_of_lt hhi,
      Nat.mod_eq_of_lt hlo, VEnv.get]
  rw [fpZeroLoads,
    Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x002") hargs hlookup]
  exact eval_fpZero _ _ _

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).1
    _ _ _ _ _ h

private theorem mainFiniteXEq_eval (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst)
      (fpEqLoads 0 32 128 160)
      (.vals [mainFiniteXEqValue yst] (mainFiniteXEqArgsState yst)) := by
  apply sound_evalExpr
  simpa [mainFiniteXEqValue, mainFiniteXEqArgsState,
    mainValidatedState_loadWord] using
    eval_fpEqLoads mainFuns (mainFiniteEnv yst) (mainValidatedState yst)
      0 32 128 160 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) rfl

private theorem mainFiniteYEq_eval (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      (fpEqLoads 64 96 192 224)
      (.vals [mainFiniteYEqValue yst] (mainFiniteYEqArgsState yst)) := by
  apply sound_evalExpr
  have h64 : loadWord (mainFiniteXEqArgsState yst).memory 64 =
      mainDecodedWord yst 64 := by
    rw [mainFiniteXEqArgsState, afterFourLoads_memory]
    exact mainValidatedState_loadWord yst 64 (by norm_num)
  have h96 : loadWord (mainFiniteXEqArgsState yst).memory 96 =
      mainDecodedWord yst 96 := by
    rw [mainFiniteXEqArgsState, afterFourLoads_memory]
    exact mainValidatedState_loadWord yst 96 (by norm_num)
  have h192 : loadWord (mainFiniteXEqArgsState yst).memory 192 =
      mainDecodedWord yst 192 := by
    rw [mainFiniteXEqArgsState, afterFourLoads_memory]
    exact mainValidatedState_loadWord yst 192 (by norm_num)
  have h224 : loadWord (mainFiniteXEqArgsState yst).memory 224 =
      mainDecodedWord yst 224 := by
    rw [mainFiniteXEqArgsState, afterFourLoads_memory]
    exact mainValidatedState_loadWord yst 224 (by norm_num)
  have h := eval_fpEqLoads ([] :: mainFuns) (mainFiniteEnv yst)
    (mainFiniteXEqArgsState yst) 64 96 192 224
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
  rw [h64, h96, h192, h224] at h
  exact h

private theorem mainFiniteYZero_eval (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYEqArgsState yst)
      (fpZeroLoads 64 96)
      (.vals [mainFiniteYZeroValue yst] (mainFiniteYZeroArgsState yst)) := by
  apply sound_evalExpr
  have h64 : loadWord (mainFiniteYEqArgsState yst).memory 64 =
      mainDecodedWord yst 64 := by
    rw [mainFiniteYEqArgsState, afterFourLoads_memory,
      mainFiniteXEqArgsState, afterFourLoads_memory]
    exact mainValidatedState_loadWord yst 64 (by norm_num)
  have h96 : loadWord (mainFiniteYEqArgsState yst).memory 96 =
      mainDecodedWord yst 96 := by
    rw [mainFiniteYEqArgsState, afterFourLoads_memory,
      mainFiniteXEqArgsState, afterFourLoads_memory]
    exact mainValidatedState_loadWord yst 96 (by norm_num)
  have h := eval_fpZeroLoads ([] :: mainFuns) (mainFiniteEnv yst)
    (mainFiniteYEqArgsState yst) 64 96
    (by norm_num) (by norm_num) rfl
  rw [h64, h96] at h
  exact h

private def finiteInfinityBody : Block Op :=
  [.exprStmt (.call "\x0012"
      [.lit (.number 0), .lit (.number 0),
        .lit (.number 0), .lit (.number 0)]),
    .exprStmt (.builtin .ret [.lit (.number 0), .lit (.number 128)])]

private theorem finiteInfinityBody_hoist :
    hoist Challenge.EvmProof.modexpExec.toDialect finiteInfinityBody = [] := by
  rfl

private theorem finiteInfinityBody_exec
    (funs : FunEnv Challenge.EvmProof.modexpExec.toDialect)
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (hlookup : lookupFun funs "\x0012" = lookupFun mainFuns "\x0012") :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V yst
      finiteInfinityBody V (finiteInfinityReturnState yst) .halt := by
  have hcallEval :
      Interp.evalExpr Challenge.EvmProof.modexpExec 65 funs V yst
        (.call "\x0012"
          [.lit (.number 0), .lit (.number 0),
            .lit (.number 0), .lit (.number 0)]) =
        .ok (.vals [] (finiteInfinityStoredState yst)) := by
    have hargs :
        Interp.evalArgs Challenge.EvmProof.modexpExec 64 funs V yst
            [.lit (.number 0), .lit (.number 0),
              .lit (.number 0), .lit (.number 0)] =
          Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
            [("\x0092", 0), ("\x0093", 0),
              ("\x0094", 0), ("\x0095", 0)] yst
            [.var "\x0092", .var "\x0093",
              .var "\x0094", .var "\x0095"] := by
      simp [Interp.evalArgs, Interp.evalExpr, EVM.litValue, VEnv.get]
    rw [Interp.evalExpr_call_of_evalArgs_lookup_eq
      (fn := "\x0012") hargs hlookup]
    exact eval_storePoint 0 0 0 0 yst
  have hcall := sound_evalExpr hcallEval
  have hzero : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      funs V (finiteInfinityStoredState yst) (.lit (.number 0))
      (.vals [0] (finiteInfinityStoredState yst)) := Step.lit
  have hsize : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      funs V (finiteInfinityStoredState yst) (.lit (.number 128))
      (.vals [128] (finiteInfinityStoredState yst)) := Step.lit
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      funs V (finiteInfinityStoredState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 128)])
      (.halt (finiteInfinityReturnState yst)) := by
    exact Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil hsize) hzero) rfl
  exact Step.seqCons (Step.exprStmt hcall)
    (Step.seqStop (Step.exprStmtHalt hret) (by decide))

private theorem mainFiniteOppositeStmt_shape : mainFiniteOppositeStmt =
    .cond (.builtin .iszero [fpEqLoads 64 96 192 224])
      finiteInfinityBody := by
  rfl

private theorem mainFiniteZeroYStmt_shape : mainFiniteZeroYStmt =
    .cond (fpZeroLoads 64 96) finiteInfinityBody := by
  rfl

private theorem mainFiniteEqualStmt_shape : mainFiniteEqualStmt =
    .cond (fpEqLoads 0 32 128 160) mainFiniteEqualBody := by
  rfl

private theorem mainFiniteEqualBody_hoist :
    hoist Challenge.EvmProof.modexpExec.toDialect mainFiniteEqualBody = [] := by
  rfl

/-- Exact corrected source execution for equal x and unequal y. -/
theorem step_mainFiniteOpposite_return (yst : EvmState)
    (hyeq : mainFiniteYEqValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteOppositeStmt (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt := by
  rw [mainFiniteOppositeStmt_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      (.builtin .iszero [fpEqLoads 64 96 192 224])
      (.vals [b2w (mainFiniteYEqValue yst = 0)]
        (mainFiniteYEqArgsState yst)) := by
    exact Step.builtinOk
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (Step.argsCons Step.argsNil (mainFiniteYEq_eval yst)) rfl
  have hseq := finiteInfinityBody_exec ([] :: [] :: mainFuns)
    (mainFiniteEnv yst) (mainFiniteYEqArgsState yst) rfl
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect finiteInfinityBody ::
        [] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYEqArgsState yst)
      finiteInfinityBody (mainFiniteEnv yst)
      (finiteInfinityReturnState (mainFiniteYEqArgsState yst)) .halt := by
    rw [finiteInfinityBody_hoist]
    exact hseq
  have hblock' := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteYEqArgsState yst)
      (.block finiteInfinityBody) (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt := by
    simpa [mainFiniteOppositeReturnState, restore] using hblock'
  have hnonzero : b2w (mainFiniteYEqValue yst = 0) ≠
      Challenge.EvmProof.modexpExec.toDialect.zero := by
    rw [hyeq]
    decide
  exact Step.ifTrue hcondition hnonzero hblock

/-- Exact corrected source execution for equal points with `y = 0`. -/
theorem step_mainFiniteZeroY_return (yst : EvmState)
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYEqArgsState yst)
      mainFiniteZeroYStmt (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt := by
  rw [mainFiniteZeroYStmt_shape]
  have hcondition := mainFiniteYZero_eval yst
  have hseq := finiteInfinityBody_exec ([] :: [] :: mainFuns)
    (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst) rfl
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect finiteInfinityBody ::
        [] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      finiteInfinityBody (mainFiniteEnv yst)
      (finiteInfinityReturnState (mainFiniteYZeroArgsState yst)) .halt := by
    rw [finiteInfinityBody_hoist]
    exact hseq
  have hblock' := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      (.block finiteInfinityBody) (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt := by
    simpa [mainFiniteZeroYReturnState, restore] using hblock'
  exact Step.ifTrue hcondition hyzero hblock

private theorem step_mainFiniteOpposite_continue (yst : EvmState)
    (hyeq : mainFiniteYEqValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteOppositeStmt (mainFiniteEnv yst)
      (mainFiniteYEqArgsState yst) .normal := by
  rw [mainFiniteOppositeStmt_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      (.builtin .iszero [fpEqLoads 64 96 192 224])
      (.vals [b2w (mainFiniteYEqValue yst = 0)]
        (mainFiniteYEqArgsState yst)) := by
    exact Step.builtinOk
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (Step.argsCons Step.argsNil (mainFiniteYEq_eval yst)) rfl
  have hzero : b2w (mainFiniteYEqValue yst = 0) =
      Challenge.EvmProof.modexpExec.toDialect.zero := by
    have hfalse : decide (mainFiniteYEqValue yst = 0) = false :=
      decide_eq_false_iff_not.mpr hyeq
    rw [b2w, hfalse]
    rfl
  exact Step.ifFalse hcondition hzero

/-- The complete equal-x dispatcher takes the corrected opposite-point branch. -/
theorem step_mainFiniteEqual_opposite (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst) mainFiniteEqualStmt
      (mainFiniteEnv yst) (mainFiniteOppositeReturnState yst) .halt := by
  rw [mainFiniteEqualStmt_shape]
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteEqualBody (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt := by
    rw [mainFiniteEqualBody_eq]
    exact Step.seqStop (step_mainFiniteOpposite_return yst hyeq) (by decide)
  have hblock' := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect)
    (show ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainFiniteEqualBody ::
        mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteEqualBody (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt from by
        rw [mainFiniteEqualBody_hoist]
        exact hseq)
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      (.block mainFiniteEqualBody) (mainFiniteEnv yst)
      (mainFiniteOppositeReturnState yst) .halt := by
    simpa [restore] using hblock'
  exact Step.ifTrue (mainFiniteXEq_eval yst) (by rw [hxeq]; decide) hblock

/-- The complete equal-x dispatcher skips the opposite test and takes the
explicit equal-point/y-zero branch. -/
theorem step_mainFiniteEqual_zeroY (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst) mainFiniteEqualStmt
      (mainFiniteEnv yst) (mainFiniteZeroYReturnState yst) .halt := by
  rw [mainFiniteEqualStmt_shape]
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteEqualBody (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt := by
    rw [mainFiniteEqualBody_eq]
    exact Step.seqCons (step_mainFiniteOpposite_continue yst hyeq)
      (Step.seqStop (step_mainFiniteZeroY_return yst hyzero) (by decide))
  have hblock' := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect)
    (show ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainFiniteEqualBody ::
        mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteEqualBody (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt from by
        rw [mainFiniteEqualBody_hoist]
        exact hseq)
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      (.block mainFiniteEqualBody) (mainFiniteEnv yst)
      (mainFiniteZeroYReturnState yst) .halt := by
    simpa [restore] using hblock'
  exact Step.ifTrue (mainFiniteXEq_eval yst) (by rw [hxeq]; decide) hblock

/-- Unequal x-coordinates skip the equal-point dispatcher after evaluating
its exact four-word comparison. -/
theorem step_mainFiniteEqual_skip (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst) mainFiniteEqualStmt
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst) .normal := by
  rw [mainFiniteEqualStmt_shape]
  exact Step.ifFalse (mainFiniteXEq_eval yst) (by rw [hxeq]; rfl)

private theorem step_mainFiniteZeroY_continue (yst : EvmState)
    (hyzero : mainFiniteYZeroValue yst = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYEqArgsState yst)
      mainFiniteZeroYStmt (mainFiniteEnv yst)
      (mainFiniteYZeroArgsState yst) .normal := by
  rw [mainFiniteZeroYStmt_shape]
  exact Step.ifFalse (mainFiniteYZero_eval yst) hyzero

/-- Compose the equal-x dispatch prefix with a caller-supplied checked
nonexceptional doubling body.  The statement is generic in the tail result so
the source classifier remains layered below the arithmetic proof. -/
theorem step_mainFiniteEqual_nonexceptional (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1)
    (hyeq : mainFiniteYEqValue yst ≠ 0)
    (hyzero : mainFiniteYZeroValue yst = 0)
    {V' : VEnv Challenge.EvmProof.modexpExec.toDialect} {st' : EvmState}
    (htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      mainFiniteDoubleBody V' st' .normal) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainValidatedState yst) mainFiniteEqualStmt
      (restore (mainFiniteEnv yst) V') st' .normal := by
  rw [mainFiniteEqualStmt_shape]
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteEqualBody V' st' .normal := by
    rw [mainFiniteEqualBody_eq]
    exact Step.seqCons (step_mainFiniteOpposite_continue yst hyeq)
      (Step.seqCons (step_mainFiniteZeroY_continue yst hyzero) htail)
  have hblock' := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect)
    (show ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect mainFiniteEqualBody ::
        mainFuns) (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteEqualBody V' st' .normal from by
        rw [mainFiniteEqualBody_hoist]
        exact hseq)
  exact Step.ifTrue (mainFiniteXEq_eval yst) (by rw [hxeq]; decide) hblock'

private theorem fourZeroWords (yst : EvmState) :
    readBytes (mainStorePointState yst 0 0 0 0).memory 0 128 =
      List.replicate 128 0 := by
  simp [mainStorePointState]
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 32 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  decide

private theorem finiteInfinityReturnState_zero (yst : EvmState) :
    (finiteInfinityReturnState yst).halted =
      some (HaltKind.ret, List.replicate 128 0) := by
  change some (HaltKind.ret,
    readBytes (mainStorePointState yst 0 0 0 0).memory 0 128) = _
  rw [fourZeroWords]

theorem mainFiniteOpposite_returned_zero_bytes (yst : EvmState) :
    (mainFiniteOppositeReturnState yst).halted =
      some (HaltKind.ret, List.replicate 128 0) :=
  finiteInfinityReturnState_zero _

theorem mainFiniteZeroY_returned_zero_bytes (yst : EvmState) :
    (mainFiniteZeroYReturnState yst).halted =
      some (HaltKind.ret, List.replicate 128 0) :=
  finiteInfinityReturnState_zero _

theorem mainFiniteOpposite_returned_codec (yst : EvmState) :
    (mainFiniteOppositeReturnState yst).halted =
      some (HaltKind.ret,
        Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (.infinity : EvmSemantics.Crypto.Bls12381.Point) |>.toList) := by
  rw [mainFiniteOpposite_returned_zero_bytes, encodeG1_infinity_toList]

theorem mainFiniteZeroY_returned_codec (yst : EvmState) :
    (mainFiniteZeroYReturnState yst).halted =
      some (HaltKind.ret,
        Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (.infinity : EvmSemantics.Crypto.Bls12381.Point) |>.toList) := by
  rw [mainFiniteZeroY_returned_zero_bytes, encodeG1_infinity_toList]

/-- Local lawful-affine opposite points classify to infinity. -/
theorem mainFiniteOpposite_affineInfinity
    (x y1 y2 : Challenge.Bls12381.ProofSupport.G1Affine.Field)
    (hopposite : y1 + y2 = 0) :
    Challenge.Bls12381.ProofSupport.G1Affine.add
      (.affine x y1) (.affine x y2) = .infinity := by
  simp [Challenge.Bls12381.ProofSupport.G1Affine.add,
    Challenge.Bls12381.ProofSupport.LawfulAffine.add, hopposite]

/-- Local lawful-affine doubling at `y = 0` classifies to infinity. -/
theorem mainFiniteZeroY_affineInfinity
    (x : Challenge.Bls12381.ProofSupport.G1Affine.Field) :
    Challenge.Bls12381.ProofSupport.G1Affine.double (.affine x 0) =
      .infinity := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
