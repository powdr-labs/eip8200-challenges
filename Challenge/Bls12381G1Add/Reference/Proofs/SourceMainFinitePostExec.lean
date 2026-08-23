import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFinitePostState
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Frozen G1ADD common post-slope execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).2.2.1
    funs V st stmt V' st' outcome h

private theorem eval_fpMulVars (V : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (yst : EvmState) (ahi alo bhi blo : U256)
    (aHiVar aLoVar bHiVar bLoVar : String)
    (haHi : V.get aHiVar = some ahi)
    (haLo : V.get aLoVar = some alo)
    (hbHi : V.get bHiVar = some bhi)
    (hbLo : V.get bLoVar = some blo) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 69 mainFuns V yst
      (.call "\x009" [.var aHiVar, .var aLoVar, .var bHiVar, .var bLoVar]) =
      .ok (.vals [(fpMulResult yst ahi alo bhi blo).1,
        (fpMulResult yst ahi alo bhi blo).2]
        (fpMulFinalState yst ahi alo bhi blo)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 68
      mainFuns V yst [.var aHiVar, .var aLoVar, .var bHiVar,
        .var bLoVar] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 68 mainFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [haHi, haLo, hbHi, hbLo]
    rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x009") hargs
    (show lookupFun mainFuns "\x009" =
      lookupFun mainFuns "\x009" by rfl)]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpMul ahi alo bhi blo yst

private theorem eval_fpSubVars (V : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (yst : EvmState) (ahi alo bhi blo : U256)
    (aHiVar aLoVar bHiVar bLoVar : String)
    (haHi : V.get aHiVar = some ahi)
    (haLo : V.get aLoVar = some alo)
    (hbHi : V.get bHiVar = some bhi)
    (hbLo : V.get bLoVar = some blo) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 mainFuns V yst
      (.call "\x005" [.var aHiVar, .var aLoVar, .var bHiVar, .var bLoVar]) =
      .ok (.vals [(fpSubValue ahi alo bhi blo).1,
        (fpSubValue ahi alo bhi blo).2] yst) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 64
      mainFuns V yst [.var aHiVar, .var aLoVar, .var bHiVar,
        .var bLoVar] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [haHi, haLo, hbHi, hbLo]
    rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x005") hargs
    (show lookupFun mainFuns "\x005" =
      lookupFun mainFuns "\x005" by rfl)]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpSub ahi alo bhi blo yst

private theorem eval_fpSubVarsLoads
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (ahi alo : U256) (aHiVar aLoVar : String) (bHi bLo : Nat)
    (haHi : V.get aHiVar = some ahi) (haLo : V.get aLoVar = some alo)
    (hbHi : bHi < 2 ^ 256) (hbLo : bLo < 2 ^ 256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 mainFuns V yst
      (.call "\x005" [.var aHiVar, .var aLoVar,
        .builtin .mload [.lit (.number bHi)],
        .builtin .mload [.lit (.number bLo)]]) =
      .ok (.vals [(fpSubValue ahi alo
        (loadWord yst.memory bHi) (loadWord yst.memory bLo)).1,
        (fpSubValue ahi alo
        (loadWord yst.memory bHi) (loadWord yst.memory bLo)).2]
        (afterTwoLoads yst bHi bLo)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 64
      mainFuns V yst [.var aHiVar, .var aLoVar,
        .builtin .mload [.lit (.number bHi)],
        .builtin .mload [.lit (.number bLo)]] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
      [("ahi", ahi), ("alo", alo),
        ("bhi", loadWord yst.memory bHi),
        ("blo", loadWord yst.memory bLo)] (afterTwoLoads yst bHi bLo)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    norm_num at hbHi hbLo
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [haHi, haLo]
    simp [afterTwoLoads, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue,
      Nat.mod_eq_of_lt hbHi, Nat.mod_eq_of_lt hbLo, VEnv.get]
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x005") hargs
    (show lookupFun mainFuns "\x005" =
      lookupFun mainFuns "\x005" by rfl)]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl]
  exact eval_fpSub _ _ _ _ _

private theorem eval_fpSubLoadsVars
    (V : VEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState)
    (aHi aLo : Nat) (bhi blo : U256) (bHiVar bLoVar : String)
    (haHi : aHi < 2 ^ 256) (haLo : aLo < 2 ^ 256)
    (hbHi : V.get bHiVar = some bhi) (hbLo : V.get bLoVar = some blo) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 mainFuns V yst
      (.call "\x005" [.builtin .mload [.lit (.number aHi)],
        .builtin .mload [.lit (.number aLo)], .var bHiVar, .var bLoVar]) =
      .ok (.vals [(fpSubValue (loadWord yst.memory aHi)
        (loadWord yst.memory aLo) bhi blo).1,
        (fpSubValue (loadWord yst.memory aHi)
        (loadWord yst.memory aLo) bhi blo).2]
        (afterTwoLoads yst aHi aLo)) := by
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 64
      mainFuns V yst [.builtin .mload [.lit (.number aHi)],
        .builtin .mload [.lit (.number aLo)], .var bHiVar, .var bLoVar] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
      [("ahi", loadWord yst.memory aHi),
        ("alo", loadWord yst.memory aLo), ("bhi", bhi), ("blo", blo)]
      (afterTwoLoads yst aHi aLo)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    norm_num at haHi haLo
    simp only [Interp.evalArgs, Interp.evalExpr]
    rw [hbHi, hbLo]
    simp [afterTwoLoads, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue,
      Nat.mod_eq_of_lt haHi, Nat.mod_eq_of_lt haLo, VEnv.get]
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x005") hargs
    (show lookupFun mainFuns "\x005" =
      lookupFun mainFuns "\x005" by rfl)]
  rw [show mainFuns = [hoist Challenge.EvmProof.modexpExec.toDialect
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
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hlamHi : base.get "\x0098" = some lam.1)
    (hlamLo : base.get "\x0099" = some lam.2) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70 mainFuns base st
      mainFinitePostStmt0 =
    .ok (mainFinitePostEnv0 base st lam, mainFinitePostState0 st lam,
      .normal) := by
  rw [show mainFinitePostStmt0 =
    .letDecl ["\x00114", "\x00115"]
      (some (.call "\x009"
        [.var "\x0098", .var "\x0099", .var "\x0098", .var "\x0099"])) by rfl,
    Interp.execStmt,
    eval_fpMulVars base st lam.1 lam.2 lam.1 lam.2
      "\x0098" "\x0099" "\x0098" "\x0099"
      hlamHi hlamLo hlamHi hlamLo]
  rfl

private theorem exec_stmt1 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 mainFuns
      (mainFinitePostEnv0 base st lam) (mainFinitePostState0 st lam)
      mainFinitePostStmt1 =
    .ok (mainFinitePostEnv1 yst base st lam,
      mainFinitePostX1ArgsState st lam, .normal) := by
  let sq := mainFinitePostLambdaSqWords st lam
  have h := eval_fpSubVarsLoads (mainFinitePostEnv0 base st lam)
    (mainFinitePostState0 st lam) sq.1 sq.2 "\x00114" "\x00115" 0 32
    (by rfl) (by rfl) (by norm_num) (by norm_num)
  rw [state0_loadWord yst st lam hread 0 (by norm_num),
    state0_loadWord yst st lam hread 32 (by norm_num)] at h
  rw [show mainFinitePostStmt1 =
    .assign ["\x00114", "\x00115"]
      (.call "\x005" [.var "\x00114", .var "\x00115",
        .builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)]]) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt2 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 mainFuns
      (mainFinitePostEnv1 yst base st lam)
      (mainFinitePostX1ArgsState st lam) mainFinitePostStmt2 =
    .ok (mainFinitePostEnv2 yst base st lam,
      mainFinitePostX2ArgsState yst st lam, .normal) := by
  let first := mainFinitePostX3FirstWords yst st lam
  have h := eval_fpSubVarsLoads (mainFinitePostEnv1 yst base st lam)
    (mainFinitePostX1ArgsState st lam) first.1 first.2
    "\x00114" "\x00115" 128 160
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
    .assign ["\x00114", "\x00115"]
      (.call "\x005" [.var "\x00114", .var "\x00115",
        .builtin .mload [.lit (.number 128)],
        .builtin .mload [.lit (.number 160)]]) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt3 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 mainFuns
      (mainFinitePostEnv2 yst base st lam)
      (mainFinitePostX2ArgsState yst st lam) mainFinitePostStmt3 =
    .ok (mainFinitePostEnv3 yst base st lam,
      mainFinitePostDeltaArgsState yst st lam, .normal) := by
  let x3 := mainFinitePostX3Words yst st lam
  have h := eval_fpSubLoadsVars (mainFinitePostEnv2 yst base st lam)
    (mainFinitePostX2ArgsState yst st lam) 0 32 x3.1 x3.2
    "\x00114" "\x00115"
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
    .letDecl ["\x00116", "\x00117"]
      (some (.call "\x005"
        [.builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)],
          .var "\x00114", .var "\x00115"])) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt4 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hlamHi : base.get "\x0098" = some lam.1)
    (hlamLo : base.get "\x0099" = some lam.2) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70 mainFuns
      (mainFinitePostEnv3 yst base st lam)
      (mainFinitePostDeltaArgsState yst st lam) mainFinitePostStmt4 =
    .ok (mainFinitePostEnv4 yst base st lam,
      mainFinitePostState1 yst st lam, .normal) := by
  let delta := mainFinitePostDeltaWords yst st lam
  have hlamHi' := hlamHi
  have hlamLo' := hlamLo
  unfold VEnv.get at hlamHi' hlamLo'
  rw [show mainFinitePostStmt4 =
    .letDecl ["\x00118", "\x00119"]
      (some (.call "\x009" [.var "\x0098", .var "\x0099",
        .var "\x00116", .var "\x00117"])) by rfl,
    Interp.execStmt,
    eval_fpMulVars (mainFinitePostEnv3 yst base st lam)
      (mainFinitePostDeltaArgsState yst st lam)
      lam.1 lam.2 delta.1 delta.2
      "\x0098" "\x0099" "\x00116" "\x00117"
      (by simp [mainFinitePostEnv3, mainFinitePostEnv2,
        mainFinitePostEnv1, mainFinitePostEnv0, hlamHi', VEnv.get,
        VEnv.setMany, VEnv.set])
      (by simp [mainFinitePostEnv3, mainFinitePostEnv2,
        mainFinitePostEnv1, mainFinitePostEnv0, hlamLo', VEnv.get,
        VEnv.setMany, VEnv.set])
      (by rfl) (by rfl)]
  rfl

private theorem exec_stmt5 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 mainFuns
      (mainFinitePostEnv4 yst base st lam)
      (mainFinitePostState1 yst st lam) mainFinitePostStmt5 =
    .ok (mainFinitePostEnv5 yst base st lam,
      mainFinitePostY1ArgsState yst st lam, .normal) := by
  let product := mainFinitePostYProductWords yst st lam
  have h := eval_fpSubVarsLoads (mainFinitePostEnv4 yst base st lam)
    (mainFinitePostState1 yst st lam) product.1 product.2
    "\x00118" "\x00119" 64 96
    (by rfl) (by rfl) (by norm_num) (by norm_num)
  rw [state1_loadWord yst st lam hread 64 (by norm_num),
    state1_loadWord yst st lam hread 96 (by norm_num)] at h
  rw [show mainFinitePostStmt5 =
    .assign ["\x00118", "\x00119"]
      (.call "\x005" [.var "\x00118", .var "\x00119",
        .builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)]]) by rfl,
    Interp.execStmt, h]
  rfl

private theorem exec_stmt6 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 mainFuns
      (mainFinitePostEnv5 yst base st lam)
      (mainFinitePostY1ArgsState yst st lam) mainFinitePostStmt6 =
    .ok (mainFinitePostEnv5 yst base st lam,
      mainFinitePostStoredState yst st lam, .normal) := by
  let x3 := mainFinitePostX3Words yst st lam
  let y3 := mainFinitePostY3Words yst st lam
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 64
      mainFuns (mainFinitePostEnv5 yst base st lam)
      (mainFinitePostY1ArgsState yst st lam)
      [.var "\x00114", .var "\x00115", .var "\x00118", .var "\x00119"] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
      [("\x0092", x3.1), ("\x0093", x3.2),
        ("\x0094", y3.1), ("\x0095", y3.2)]
      (mainFinitePostY1ArgsState yst st lam)
      [.var "\x0092", .var "\x0093", .var "\x0094", .var "\x0095"] := by
    rfl
  rw [show mainFinitePostStmt6 =
    .exprStmt (.call "\x0012" [.var "\x00114", .var "\x00115",
      .var "\x00118", .var "\x00119"]) by rfl,
    Interp.execStmt,
    Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x0012") hargs
      (show lookupFun mainFuns "\x0012" =
        lookupFun mainFuns "\x0012" by rfl)]
  change (do
      let __do_lift ← Interp.evalExpr Challenge.EvmProof.modexpExec 64
        mainFuns [("\x0092", x3.1), ("\x0093", x3.2),
          ("\x0094", y3.1), ("\x0095", y3.2)]
        (mainFinitePostY1ArgsState yst st lam)
        (.call "\x0012" [.var "\x0092", .var "\x0093",
          .var "\x0094", .var "\x0095"])
      match __do_lift with
      | .vals [] st1 => .ok (mainFinitePostEnv5 yst base st lam, st1,
          Outcome.normal)
      | .vals _ _ => .stuck
      | .halt st1 => .ok (mainFinitePostEnv5 yst base st lam, st1,
          Outcome.halt)) = _
  rw [eval_storePoint x3.1 x3.2 y3.1 y3.2]
  rfl

private theorem exec_stmt7 (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect) :
    Interp.execStmt Challenge.EvmProof.modexpExec 66 mainFuns
      (mainFinitePostEnv5 yst base st lam)
      (mainFinitePostStoredState yst st lam) mainFinitePostStmt7 =
    .ok (mainFinitePostEnv5 yst base st lam,
      mainFinitePostReturnState yst st lam, .halt) := by
  rw [show mainFinitePostStmt7 =
    .exprStmt (.builtin .ret [.lit (.number 0), .lit (.number 128)]) by rfl]
  simp only [Interp.execStmt, Interp.evalExpr, Interp.evalArgs,
    EVM.litValue, Challenge.EvmProof.modexpExec,
    Challenge.EvmProof.modexpBuiltinFn, stepOp]
  rfl

/-- Exact execution of the eight common post-slope statements. -/
theorem step_mainFinitePostBody (yst st : EvmState) (lam : U256 × U256)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hlamHi : base.get "\x0098" = some lam.1)
    (hlamLo : base.get "\x0099" = some lam.2)
    (hread : ∀ offset, offset + 32 ≤ 1024 →
      loadWord st.memory offset = mainDecodedWord yst offset) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
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
