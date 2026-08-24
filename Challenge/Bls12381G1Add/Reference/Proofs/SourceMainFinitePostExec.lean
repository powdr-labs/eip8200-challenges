import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFinitePostState
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Frozen G1ADD common post-slope execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.YulProof.ClosedEvm.exec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.YulProof.ClosedEvm.exec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.YulProof.ClosedEvm.exec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.YulProof.ClosedEvm.builtinFn_sound hbuiltin) n).2.2.1
    funs V st stmt V' st' outcome h

private theorem eval_fpMulVars (V : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (yst : EvmState) (ahi alo bhi blo : U256)
    (aHiVar aLoVar bHiVar bLoVar : String)
    (haHi : V.get aHiVar = some ahi)
    (haLo : V.get aLoVar = some alo)
    (hbHi : V.get bHiVar = some bhi)
    (hbLo : V.get bLoVar = some blo) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 69 mainFuns V yst
      (.call "\x009" [.var aHiVar, .var aLoVar, .var bHiVar, .var bLoVar]) =
      .ok (.vals [(fpMulResult yst ahi alo bhi blo).1,
        (fpMulResult yst ahi alo bhi blo).2]
        (fpMulFinalState yst ahi alo bhi blo)) := by
  have hargs : Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 68
      mainFuns V yst [.var aHiVar, .var aLoVar, .var bHiVar,
        .var bLoVar] =
    Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 68 mainFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [haHi, haLo, hbHi, hbLo]
    rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x009") hargs
    (show lookupFun mainFuns "\x009" =
      lookupFun mainFuns "\x009" by rfl)]
  rw [show mainFuns = [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpMul ahi alo bhi blo yst

private theorem eval_fpSubVars (V : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (yst : EvmState) (ahi alo bhi blo : U256)
    (aHiVar aLoVar bHiVar bLoVar : String)
    (haHi : V.get aHiVar = some ahi)
    (haLo : V.get aLoVar = some alo)
    (hbHi : V.get bHiVar = some bhi)
    (hbLo : V.get bLoVar = some blo) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65 mainFuns V yst
      (.call "\x005" [.var aHiVar, .var aLoVar, .var bHiVar, .var bLoVar]) =
      .ok (.vals [(fpSubValue ahi alo bhi blo).1,
        (fpSubValue ahi alo bhi blo).2] yst) := by
  have hargs : Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64
      mainFuns V yst [.var aHiVar, .var aLoVar, .var bHiVar,
        .var bLoVar] =
    Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 mainFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [haHi, haLo, hbHi, hbLo]
    rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x005") hargs
    (show lookupFun mainFuns "\x005" =
      lookupFun mainFuns "\x005" by rfl)]
  rw [show mainFuns = [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpSub ahi alo bhi blo yst

private theorem eval_fpSubVarsLoads
    (V : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect) (yst : EvmState)
    (ahi alo : U256) (aHiVar aLoVar : String) (bHi bLo : Nat)
    (haHi : V.get aHiVar = some ahi) (haLo : V.get aLoVar = some alo)
    (hbHi : bHi < 2 ^ 256) (hbLo : bLo < 2 ^ 256) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65 mainFuns V yst
      (.call "\x005" [.var aHiVar, .var aLoVar,
        .builtin .mload [.lit (.number bHi)],
        .builtin .mload [.lit (.number bLo)]]) =
      .ok (.vals [(fpSubValue ahi alo
        (loadWord yst.memory bHi) (loadWord yst.memory bLo)).1,
        (fpSubValue ahi alo
        (loadWord yst.memory bHi) (loadWord yst.memory bLo)).2]
        (afterTwoLoads yst bHi bLo)) := by
  have hargs : Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64
      mainFuns V yst [.var aHiVar, .var aLoVar,
        .builtin .mload [.lit (.number bHi)],
        .builtin .mload [.lit (.number bLo)]] =
    Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 mainFuns
      [("ahi", ahi), ("alo", alo),
        ("bhi", loadWord yst.memory bHi),
        ("blo", loadWord yst.memory bLo)] (afterTwoLoads yst bHi bLo)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    norm_num at hbHi hbLo
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [haHi, haLo]
    simp [afterTwoLoads, Challenge.YulProof.ClosedEvm.exec,
      Challenge.YulProof.ClosedEvm.builtinFn, stepOp, EVM.litValue,
      Nat.mod_eq_of_lt hbHi, Nat.mod_eq_of_lt hbLo, VEnv.get]
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x005") hargs
    (show lookupFun mainFuns "\x005" =
      lookupFun mainFuns "\x005" by rfl)]
  rw [show mainFuns = [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpSub _ _ _ _ _

private theorem eval_fpSubLoadsVars
    (V : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect) (yst : EvmState)
    (aHi aLo : Nat) (bhi blo : U256) (bHiVar bLoVar : String)
    (haHi : aHi < 2 ^ 256) (haLo : aLo < 2 ^ 256)
    (hbHi : V.get bHiVar = some bhi) (hbLo : V.get bLoVar = some blo) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65 mainFuns V yst
      (.call "\x005" [.builtin .mload [.lit (.number aHi)],
        .builtin .mload [.lit (.number aLo)], .var bHiVar, .var bLoVar]) =
      .ok (.vals [(fpSubValue (loadWord yst.memory aHi)
        (loadWord yst.memory aLo) bhi blo).1,
        (fpSubValue (loadWord yst.memory aHi)
        (loadWord yst.memory aLo) bhi blo).2]
        (afterTwoLoads yst aHi aLo)) := by
  have hargs : Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64
      mainFuns V yst [.builtin .mload [.lit (.number aHi)],
        .builtin .mload [.lit (.number aLo)], .var bHiVar, .var bLoVar] =
    Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 mainFuns
      [("ahi", loadWord yst.memory aHi),
        ("alo", loadWord yst.memory aLo), ("bhi", bhi), ("blo", blo)]
      (afterTwoLoads yst aHi aLo)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    norm_num at haHi haLo
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [hbHi, hbLo]
    simp [afterTwoLoads, Challenge.YulProof.ClosedEvm.exec,
      Challenge.YulProof.ClosedEvm.builtinFn, stepOp, EVM.litValue,
      Nat.mod_eq_of_lt haHi, Nat.mod_eq_of_lt haLo, VEnv.get]
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x005") hargs
    (show lookupFun mainFuns "\x005" =
      lookupFun mainFuns "\x005" by rfl)]
  rw [show mainFuns = [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpSub _ _ _ _ _

private theorem state0_loadWord (yst st : EvmState) (lam : U256 × U256)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (mainFinitePostState0 st lam).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFinitePostState0,
    fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hend]
  exact hread offset hend

private theorem state1_loadWord (yst st : EvmState) (lam : U256 × U256)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (mainFinitePostState1 yst st lam).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFinitePostState1,
    fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hend]
  rw [mainFinitePostDeltaArgsState, afterTwoLoads_memory,
    mainFinitePostX2ArgsState, afterTwoLoads_memory,
    mainFinitePostX1ArgsState, afterTwoLoads_memory]
  exact state0_loadWord yst st lam hread offset hend

private theorem exec_stmt0 (_yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (hlamHi : base.get "\x00101" = some lam.1)
    (hlamLo : base.get "\x00102" = some lam.2) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 70 mainFuns base st
      mainFinitePostStmt0 =
    .ok (mainFinitePostEnv0 base st lam, mainFinitePostState0 st lam,
      .normal) := by
  rw [show mainFinitePostStmt0 =
    .letDecl ["\x00117", "\x00118"]
      (some (.call "\x009"
        [.var "\x00101", .var "\x00102", .var "\x00101", .var "\x00102"])) by rfl,
    Interp.execStmt,
    eval_fpMulVars base st lam.1 lam.2 lam.1 lam.2
      "\x00101" "\x00102" "\x00101" "\x00102"
      hlamHi hlamLo hlamHi hlamLo]
  rfl

private theorem exec_stmt1 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 mainFuns
      (mainFinitePostEnv0 base st lam) (mainFinitePostState0 st lam)
      mainFinitePostStmt1 =
    .ok (mainFinitePostEnv1 yst base st lam,
      mainFinitePostX1ArgsState st lam, .normal) := by
  let sq := mainFinitePostLambdaSqWords st lam
  have h := eval_fpSubVarsLoads (mainFinitePostEnv0 base st lam)
    (mainFinitePostState0 st lam) sq.1 sq.2 "\x00117" "\x00118" 0 32
    (by rfl) (by rfl) (by norm_num) (by norm_num)
  rw [state0_loadWord yst st lam hread 0 (by norm_num),
    state0_loadWord yst st lam hread 32 (by norm_num)] at h
  rw [show mainFinitePostStmt1 =
    .assign ["\x00117", "\x00118"]
      (.call "\x005" [.var "\x00117", .var "\x00118",
        .builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)]]) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt2 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 mainFuns
      (mainFinitePostEnv1 yst base st lam)
      (mainFinitePostX1ArgsState st lam) mainFinitePostStmt2 =
    .ok (mainFinitePostEnv2 yst base st lam,
      mainFinitePostX2ArgsState yst st lam, .normal) := by
  let first := mainFinitePostX3FirstWords yst st lam
  have h := eval_fpSubVarsLoads (mainFinitePostEnv1 yst base st lam)
    (mainFinitePostX1ArgsState st lam) first.1 first.2
    "\x00117" "\x00118" 128 160
    (by rfl) (by rfl) (by norm_num) (by norm_num)
  have h128 : loadWord (mainFinitePostX1ArgsState st lam).memory 128 =
      mainDecodedWord yst 128 := by
    rw [mainFinitePostX1ArgsState, afterTwoLoads_memory]
    exact state0_loadWord yst st lam hread 128 (by norm_num)
  have h160 : loadWord (mainFinitePostX1ArgsState st lam).memory 160 =
      mainDecodedWord yst 160 := by
    rw [mainFinitePostX1ArgsState, afterTwoLoads_memory]
    exact state0_loadWord yst st lam hread 160 (by norm_num)
  rw [h128, h160] at h
  rw [show mainFinitePostStmt2 =
    .assign ["\x00117", "\x00118"]
      (.call "\x005" [.var "\x00117", .var "\x00118",
        .builtin .mload [.lit (.number 128)],
        .builtin .mload [.lit (.number 160)]]) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt3 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 mainFuns
      (mainFinitePostEnv2 yst base st lam)
      (mainFinitePostX2ArgsState yst st lam) mainFinitePostStmt3 =
    .ok (mainFinitePostEnv3 yst base st lam,
      mainFinitePostDeltaArgsState yst st lam, .normal) := by
  let x3 := mainFinitePostX3Words yst st lam
  have h := eval_fpSubLoadsVars (mainFinitePostEnv2 yst base st lam)
    (mainFinitePostX2ArgsState yst st lam) 0 32 x3.1 x3.2
    "\x00117" "\x00118"
    (by norm_num) (by norm_num) (by rfl) (by rfl)
  have h0 : loadWord (mainFinitePostX2ArgsState yst st lam).memory 0 =
      mainDecodedWord yst 0 := by
    rw [mainFinitePostX2ArgsState, afterTwoLoads_memory,
      mainFinitePostX1ArgsState, afterTwoLoads_memory]
    exact state0_loadWord yst st lam hread 0 (by norm_num)
  have h32 : loadWord (mainFinitePostX2ArgsState yst st lam).memory 32 =
      mainDecodedWord yst 32 := by
    rw [mainFinitePostX2ArgsState, afterTwoLoads_memory,
      mainFinitePostX1ArgsState, afterTwoLoads_memory]
    exact state0_loadWord yst st lam hread 32 (by norm_num)
  rw [h0, h32] at h
  rw [show mainFinitePostStmt3 =
    .letDecl ["\x00119", "\x00120"]
      (some (.call "\x005"
        [.builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)],
          .var "\x00117", .var "\x00118"])) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt4 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (hlamHi : base.get "\x00101" = some lam.1)
    (hlamLo : base.get "\x00102" = some lam.2) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 70 mainFuns
      (mainFinitePostEnv3 yst base st lam)
      (mainFinitePostDeltaArgsState yst st lam) mainFinitePostStmt4 =
    .ok (mainFinitePostEnv4 yst base st lam,
      mainFinitePostState1 yst st lam, .normal) := by
  let delta := mainFinitePostDeltaWords yst st lam
  have hlamHi' := hlamHi
  have hlamLo' := hlamLo
  unfold VEnv.get at hlamHi' hlamLo'
  rw [show mainFinitePostStmt4 =
    .letDecl ["\x00121", "\x00122"]
      (some (.call "\x009" [.var "\x00101", .var "\x00102",
        .var "\x00119", .var "\x00120"])) by rfl,
    Interp.execStmt,
    eval_fpMulVars (mainFinitePostEnv3 yst base st lam)
      (mainFinitePostDeltaArgsState yst st lam)
      lam.1 lam.2 delta.1 delta.2
      "\x00101" "\x00102" "\x00119" "\x00120"
      (by simp [mainFinitePostEnv3, mainFinitePostEnv2,
        mainFinitePostEnv1, mainFinitePostEnv0, hlamHi', VEnv.get,
        VEnv.setMany, VEnv.set])
      (by simp [mainFinitePostEnv3, mainFinitePostEnv2,
        mainFinitePostEnv1, mainFinitePostEnv0, hlamLo', VEnv.get,
        VEnv.setMany, VEnv.set])
      (by rfl) (by rfl)]
  rfl

private theorem exec_stmt5 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 mainFuns
      (mainFinitePostEnv4 yst base st lam)
      (mainFinitePostState1 yst st lam) mainFinitePostStmt5 =
    .ok (mainFinitePostEnv5 yst base st lam,
      mainFinitePostY1ArgsState yst st lam, .normal) := by
  let product := mainFinitePostYProductWords yst st lam
  have h := eval_fpSubVarsLoads (mainFinitePostEnv4 yst base st lam)
    (mainFinitePostState1 yst st lam) product.1 product.2
    "\x00121" "\x00122" 64 96
    (by rfl) (by rfl) (by norm_num) (by norm_num)
  rw [state1_loadWord yst st lam hread 64 (by norm_num),
    state1_loadWord yst st lam hread 96 (by norm_num)] at h
  rw [show mainFinitePostStmt5 =
    .assign ["\x00121", "\x00122"]
      (.call "\x005" [.var "\x00121", .var "\x00122",
        .builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)]]) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt6 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 mainFuns
      (mainFinitePostEnv5 yst base st lam)
      (mainFinitePostY1ArgsState yst st lam) mainFinitePostStmt6 =
    .ok (mainFinitePostEnv5 yst base st lam,
      mainFinitePostStoredState yst st lam, .normal) := by
  let x3 := mainFinitePostX3Words yst st lam
  let y3 := mainFinitePostY3Words yst st lam
  have hargs : Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64
      mainFuns (mainFinitePostEnv5 yst base st lam)
      (mainFinitePostY1ArgsState yst st lam)
      [.var "\x00117", .var "\x00118", .var "\x00121", .var "\x00122"] =
    Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 mainFuns
      [("\x0095", x3.1), ("\x0096", x3.2),
        ("\x0097", y3.1), ("\x0098", y3.2)]
      (mainFinitePostY1ArgsState yst st lam)
      [.var "\x0095", .var "\x0096", .var "\x0097", .var "\x0098"] := by
    rfl
  rw [show mainFinitePostStmt6 =
    .exprStmt (.call "\x0012" [.var "\x00117", .var "\x00118",
      .var "\x00121", .var "\x00122"]) by rfl,
    Interp.execStmt,
    Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x0012") hargs
      (show lookupFun mainFuns "\x0012" =
        lookupFun mainFuns "\x0012" by rfl)]
  change (do
      let __do_lift ← Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 64
        mainFuns [("\x0095", x3.1), ("\x0096", x3.2),
          ("\x0097", y3.1), ("\x0098", y3.2)]
        (mainFinitePostY1ArgsState yst st lam)
        (.call "\x0012" [.var "\x0095", .var "\x0096",
          .var "\x0097", .var "\x0098"])
      match __do_lift with
      | .vals [] st1 => .ok (mainFinitePostEnv5 yst base st lam, st1,
          Outcome.normal)
      | .vals _ _ => .stuck
      | .halt st1 => .ok (mainFinitePostEnv5 yst base st lam, st1,
          Outcome.halt)) = _
  rw [eval_storePoint x3.1 x3.2 y3.1 y3.2]
  rfl

private theorem exec_stmt7 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 mainFuns
      (mainFinitePostEnv5 yst base st lam)
      (mainFinitePostStoredState yst st lam) mainFinitePostStmt7 =
    .ok (mainFinitePostEnv5 yst base st lam,
      mainFinitePostReturnState yst st lam, .halt) := by
  rw [show mainFinitePostStmt7 =
    .exprStmt (.builtin .ret [.lit (.number 0), .lit (.number 128)]) by rfl]
  simp only [Interp.execStmt, Interp.evalExpr, Interp.evalArgs,
    EVM.litValue, Challenge.YulProof.ClosedEvm.exec,
    Challenge.YulProof.ClosedEvm.builtinFn, stepOp]
  rfl

/-- Exact execution of the eight common post-slope statements. -/
theorem step_mainFinitePostBody (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.YulProof.ClosedEvm.exec.toDialect)
    (hlamHi : base.get "\x00101" = some lam.1)
    (hlamLo : base.get "\x00102" = some lam.2)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    ExecStmts Challenge.YulProof.ClosedEvm.exec.toDialect mainFuns
      base st mainFinitePostBody (mainFinitePostEnv5 yst base st lam)
      (mainFinitePostReturnState yst st lam) .halt := by
  rw [mainFinitePostBody_eq]
  exact Step.seqCons (sound_execStmt
    (exec_stmt0 yst st lam base hlamHi hlamLo))
    (Step.seqCons (sound_execStmt (exec_stmt1 yst st lam base hread))
      (Step.seqCons (sound_execStmt (exec_stmt2 yst st lam base hread))
        (Step.seqCons (sound_execStmt (exec_stmt3 yst st lam base hread))
          (Step.seqCons (sound_execStmt
              (exec_stmt4 yst st lam base hlamHi hlamLo))
            (Step.seqCons (sound_execStmt (exec_stmt5 yst st lam base hread))
              (Step.seqCons (sound_execStmt (exec_stmt6 yst st lam base))
                (Step.seqStop (sound_execStmt
                  (exec_stmt7 yst st lam base)) (by decide))))))))

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
