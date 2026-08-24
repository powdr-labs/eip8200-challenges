import Challenge.Bls12381G1Add.Reference.Proofs.SourceOnCurveDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Frozen G1ADD `onCurve` execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def onCurveLhsEnv (yst : EvmState) (xHi xLo yHi yLo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x0089", (onCurveLhsWords yst yHi yLo).1),
    ("\x0090", (onCurveLhsWords yst yHi yLo).2)] ++
    onCurveInitialEnv xHi xLo yHi yLo

def onCurveX2Env (yst : EvmState) (xHi xLo yHi yLo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x0091", (onCurveX2Words yst xHi xLo yHi yLo).1),
    ("\x0092", (onCurveX2Words yst xHi xLo yHi yLo).2)] ++
    onCurveLhsEnv yst xHi xLo yHi yLo

def onCurveCubeEnv (yst : EvmState) (xHi xLo yHi yLo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x0093", (onCurveRhsCubeWords yst xHi xLo yHi yLo).1),
    ("\x0094", (onCurveRhsCubeWords yst xHi xLo yHi yLo).2)] ++
    onCurveX2Env yst xHi xLo yHi yLo

def onCurveRhsEnv (yst : EvmState) (xHi xLo yHi yLo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  VEnv.setMany (onCurveCubeEnv yst xHi xLo yHi yLo)
    ["\x0093", "\x0094"]
    [(onCurveRhsWords yst xHi xLo yHi yLo).1,
      (onCurveRhsWords yst xHi xLo yHi yLo).2]

def onCurveReturnEnv (yst : EvmState) (xHi xLo yHi yLo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  VEnv.setMany (onCurveRhsEnv yst xHi xLo yHi yLo) ["\x0088"]
    [onCurveResult yst xHi xLo yHi yLo]

private theorem onCurveStmt0_shape : onCurveStmt0 =
    .letDecl ["\x0089", "\x0090"]
      (some (.call "\x009"
        [.var "\x0086", .var "\x0087", .var "\x0086", .var "\x0087"])) := by
  rfl

theorem exec_onCurveStmt0 (xHi xLo yHi yLo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 69 onCurveBodyFuns
      (onCurveInitialEnv xHi xLo yHi yLo) yst onCurveStmt0 =
    .ok (onCurveLhsEnv yst xHi xLo yHi yLo,
      onCurveState1 yst yHi yLo, .normal) := by
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 onCurveBodyFuns
          (onCurveInitialEnv xHi xLo yHi yLo) yst
          [.var "\x0086", .var "\x0087", .var "\x0086", .var "\x0087"] =
        Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 onCurveFuns
          [("ahi", yHi), ("alo", yLo), ("bhi", yHi), ("blo", yLo)] yst
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hlookup : lookupFun onCurveBodyFuns "\x009" =
      lookupFun onCurveFuns "\x009" := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup
  rw [onCurveStmt0_shape, Interp.execStmt, hcall]
  rw [show onCurveFuns =
    [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
      Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul yHi yLo yHi yLo yst]
  rfl

private theorem onCurveStmt1_shape : onCurveStmt1 =
    .letDecl ["\x0091", "\x0092"]
      (some (.call "\x009"
        [.var "\x0084", .var "\x0085", .var "\x0084", .var "\x0085"])) := by
  rfl

theorem exec_onCurveStmt1 (xHi xLo yHi yLo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 69 onCurveBodyFuns
      (onCurveLhsEnv yst xHi xLo yHi yLo)
      (onCurveState1 yst yHi yLo) onCurveStmt1 =
    .ok (onCurveX2Env yst xHi xLo yHi yLo,
      onCurveState2 yst xHi xLo yHi yLo, .normal) := by
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 onCurveBodyFuns
          (onCurveLhsEnv yst xHi xLo yHi yLo)
          (onCurveState1 yst yHi yLo)
          [.var "\x0084", .var "\x0085", .var "\x0084", .var "\x0085"] =
        Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 onCurveFuns
          [("ahi", xHi), ("alo", xLo), ("bhi", xHi), ("blo", xLo)]
          (onCurveState1 yst yHi yLo)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hlookup : lookupFun onCurveBodyFuns "\x009" =
      lookupFun onCurveFuns "\x009" := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup
  rw [onCurveStmt1_shape, Interp.execStmt, hcall]
  rw [show onCurveFuns =
    [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
      Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul xHi xLo xHi xLo (onCurveState1 yst yHi yLo)]
  rfl

private theorem onCurveStmt2_shape : onCurveStmt2 =
    .letDecl ["\x0093", "\x0094"]
      (some (.call "\x009"
        [.var "\x0091", .var "\x0092", .var "\x0084", .var "\x0085"])) := by
  rfl

theorem exec_onCurveStmt2 (xHi xLo yHi yLo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 69 onCurveBodyFuns
      (onCurveX2Env yst xHi xLo yHi yLo)
      (onCurveState2 yst xHi xLo yHi yLo) onCurveStmt2 =
    .ok (onCurveCubeEnv yst xHi xLo yHi yLo,
      onCurveFinalState yst xHi xLo yHi yLo, .normal) := by
  let x2 := onCurveX2Words yst xHi xLo yHi yLo
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 onCurveBodyFuns
          (onCurveX2Env yst xHi xLo yHi yLo)
          (onCurveState2 yst xHi xLo yHi yLo)
          [.var "\x0091", .var "\x0092", .var "\x0084", .var "\x0085"] =
        Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 67 onCurveFuns
          [("ahi", x2.1), ("alo", x2.2), ("bhi", xHi), ("blo", xLo)]
          (onCurveState2 yst xHi xLo yHi yLo)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hlookup : lookupFun onCurveBodyFuns "\x009" =
      lookupFun onCurveFuns "\x009" := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x009") hargs hlookup
  rw [onCurveStmt2_shape, Interp.execStmt, hcall]
  rw [show onCurveFuns =
    [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
      Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpMul x2.1 x2.2 xHi xLo
    (onCurveState2 yst xHi xLo yHi yLo)]
  rfl

private theorem onCurveStmt3_shape : onCurveStmt3 =
    .assign ["\x0093", "\x0094"]
      (.call "\x004"
        [.var "\x0093", .var "\x0094", .lit (.number 0),
          .lit (.number 4)]) := by
  rfl

theorem exec_onCurveStmt3 (xHi xLo yHi yLo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 65 onCurveBodyFuns
      (onCurveCubeEnv yst xHi xLo yHi yLo)
      (onCurveFinalState yst xHi xLo yHi yLo) onCurveStmt3 =
    .ok (onCurveRhsEnv yst xHi xLo yHi yLo,
      onCurveFinalState yst xHi xLo yHi yLo, .normal) := by
  let cube := onCurveRhsCubeWords yst xHi xLo yHi yLo
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 63 onCurveBodyFuns
          (onCurveCubeEnv yst xHi xLo yHi yLo)
          (onCurveFinalState yst xHi xLo yHi yLo)
          [.var "\x0093", .var "\x0094", .lit (.number 0),
            .lit (.number 4)] =
        Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 63 onCurveFuns
          [("ahi", cube.1), ("alo", cube.2), ("bhi", 0), ("blo", 4)]
          (onCurveFinalState yst xHi xLo yHi yLo)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hlookup : lookupFun onCurveBodyFuns "\x004" =
      lookupFun onCurveFuns "\x004" := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup
  rw [onCurveStmt3_shape, Interp.execStmt, hcall]
  rw [show onCurveFuns =
    [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
      Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpAdd cube.1 cube.2 0 4]
  rfl

private theorem onCurveStmt4_shape : onCurveStmt4 =
    .assign ["\x0088"]
      (.call "\x003"
        [.var "\x0089", .var "\x0090", .var "\x0093", .var "\x0094"]) := by
  rfl

theorem exec_onCurveStmt4 (xHi xLo yHi yLo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 65 onCurveBodyFuns
      (onCurveRhsEnv yst xHi xLo yHi yLo)
      (onCurveFinalState yst xHi xLo yHi yLo) onCurveStmt4 =
    .ok (onCurveReturnEnv yst xHi xLo yHi yLo,
      onCurveFinalState yst xHi xLo yHi yLo, .normal) := by
  let lhs := onCurveLhsWords yst yHi yLo
  let rhs := onCurveRhsWords yst xHi xLo yHi yLo
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 63 onCurveBodyFuns
          (onCurveRhsEnv yst xHi xLo yHi yLo)
          (onCurveFinalState yst xHi xLo yHi yLo)
          [.var "\x0089", .var "\x0090", .var "\x0093", .var "\x0094"] =
        Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 63 onCurveFuns
          [("ahi", lhs.1), ("alo", lhs.2),
            ("bhi", rhs.1), ("blo", rhs.2)]
          (onCurveFinalState yst xHi xLo yHi yLo)
          [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  have hlookup : lookupFun onCurveBodyFuns "\x003" =
      lookupFun onCurveFuns "\x003" := by
    rfl
  have hcall := Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x003") hargs hlookup
  rw [onCurveStmt4_shape, Interp.execStmt, hcall]
  rw [show onCurveFuns =
    [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
      Compilation.referenceCompiledBlock] by rfl]
  rw [eval_fpEq lhs.1 lhs.2 rhs.1 rhs.2]
  rfl

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.YulProof.ClosedEvm.exec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.YulProof.ClosedEvm.exec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.YulProof.ClosedEvm.exec)
    (fun _ _ _ _ hbuiltin =>
      (Challenge.YulProof.ClosedEvm.exec_lawful _ _ _ _).mpr hbuiltin) n).2.2.1
    funs V st stmt V' st' outcome h

def onCurveBodyResultEnv (yst : EvmState) (xHi xLo yHi yLo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  restore (onCurveInitialEnv xHi xLo yHi yLo)
    (onCurveReturnEnv yst xHi xLo yHi yLo)

/-- The five frozen statements form a checked closed-dialect source derivation.
Each local arithmetic helper is first verified with the executable Yul
interpreter, then transported through its one-way soundness theorem; no common
fuel is assumed between sibling source calls. -/
theorem step_onCurveBody (xHi xLo yHi yLo : U256) (yst : EvmState) :
    ExecStmt Challenge.YulProof.ClosedEvm.exec.toDialect onCurveFuns
      (onCurveInitialEnv xHi xLo yHi yLo) yst (.block onCurveBody)
      (onCurveBodyResultEnv yst xHi xLo yHi yLo)
      (onCurveFinalState yst xHi xLo yHi yLo) .normal := by
  have h0 := sound_execStmt (exec_onCurveStmt0 xHi xLo yHi yLo yst)
  have h1 := sound_execStmt (exec_onCurveStmt1 xHi xLo yHi yLo yst)
  have h2 := sound_execStmt (exec_onCurveStmt2 xHi xLo yHi yLo yst)
  have h3 := sound_execStmt (exec_onCurveStmt3 xHi xLo yHi yLo yst)
  have h4 := sound_execStmt (exec_onCurveStmt4 xHi xLo yHi yLo yst)
  have hstmts :
      ExecStmts Challenge.YulProof.ClosedEvm.exec.toDialect onCurveBodyFuns
        (onCurveInitialEnv xHi xLo yHi yLo) yst
        [onCurveStmt0, onCurveStmt1, onCurveStmt2, onCurveStmt3,
          onCurveStmt4]
        (onCurveReturnEnv yst xHi xLo yHi yLo)
        (onCurveFinalState yst xHi xLo yHi yLo) .normal :=
    Step.seqCons h0 (Step.seqCons h1 (Step.seqCons h2
      (Step.seqCons h3 (Step.seqCons h4 Step.seqNil))))
  rw [← onCurveBody_eq] at hstmts
  rw [← onCurveBodyFuns_eq] at hstmts
  have hblock := Step.block
    (D := Challenge.YulProof.ClosedEvm.exec.toDialect) hstmts
  simpa only [onCurveBodyResultEnv] using hblock

theorem onCurveBodyResultEnv_yes (yst : EvmState)
    (xHi xLo yHi yLo : U256) :
    (VEnv.get (onCurveBodyResultEnv yst xHi xLo yHi yLo) "\x0088").getD 0 =
      onCurveResult yst xHi xLo yHi yLo := by
  rfl

/-- Relational source-execution theorem consumed by the enclosing G1ADD proof.
The frozen helper returns its exact word predicate after three local `fpMul`
calls and leaves their final memory state observable. -/
theorem step_onCurve (xHi xLo yHi yLo : U256) (yst : EvmState) :
    EvalExpr Challenge.YulProof.ClosedEvm.exec.toDialect onCurveFuns
      [("xHi", xHi), ("xLo", xLo), ("yHi", yHi), ("yLo", yLo)] yst
      (.call "\x0011" [.var "xHi", .var "xLo", .var "yHi", .var "yLo"])
      (.vals [onCurveResult yst xHi xLo yHi yLo]
        (onCurveFinalState yst xHi xLo yHi yLo)) := by
  have hargsEval :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 8 onCurveFuns
        [("xHi", xHi), ("xLo", xLo), ("yHi", yHi), ("yLo", yLo)] yst
        [.var "xHi", .var "xLo", .var "yHi", .var "yLo"] =
      .ok (.vals [xHi, xLo, yHi, yLo] yst) := by
    rfl
  have hargs := (Interp.sound_all_of
    (E := Challenge.YulProof.ClosedEvm.exec)
    (fun _ _ _ _ hbuiltin =>
      (Challenge.YulProof.ClosedEvm.exec_lawful _ _ _ _).mpr hbuiltin) 8).2.1
    _ _ _ _ _ hargsEval
  have hcall := Step.callOk hargs lookup_onCurve (by rfl)
    (step_onCurveBody xHi xLo yHi yLo yst) (Or.inl rfl)
  change EvalExpr Challenge.YulProof.ClosedEvm.exec.toDialect onCurveFuns
      [("xHi", xHi), ("xLo", xLo), ("yHi", yHi), ("yLo", yLo)] yst
      (.call "\x0011" [.var "xHi", .var "xLo", .var "yHi", .var "yLo"])
      (.vals
        [(VEnv.get (onCurveBodyResultEnv yst xHi xLo yHi yLo)
          "\x0088").getD 0]
        (onCurveFinalState yst xHi xLo yHi yLo)) at hcall
  rw [onCurveBodyResultEnv_yes] at hcall
  exact hcall

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
