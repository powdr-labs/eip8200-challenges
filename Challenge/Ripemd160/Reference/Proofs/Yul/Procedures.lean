import Challenge.Ripemd160.Reference.Proofs.Yul.Interpreter
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCorrect
import YulEvmCompiler.StateRel

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Relational contracts for RIPEMD-160 Yul procedures

The public lemmas in this file retain only selected memory observations. Exact intermediate
`EvmState` constructors are confined to small leaf proofs.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Yul.Procedures

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open Interpreter

private theorem evalExpr_of_interp {fuel : Nat} {funs : FunEnv localDialect}
    {V : VEnv localDialect} {st : EvmState} {e : Expr Op} {result}
    (h : Interp.evalExpr localExec fuel funs V st e = .ok result) :
    EvalExpr localDialect funs V st e result :=
  (Interp.sound_all localExec_lawful fuel).1 _ _ _ _ _ h

private theorem execStmt_of_interp {fuel : Nat} {funs : FunEnv localDialect}
    {V V' : VEnv localDialect} {st st' : EvmState} {stmt : Stmt Op} {outcome}
    (h : Interp.execStmt localExec fuel funs V st stmt = .ok (V', st', outcome)) :
    ExecStmt localDialect funs V st stmt V' st' outcome :=
  (Interp.sound_all localExec_lawful fuel).2.2.1 _ _ _ _ _ _ _ h

private theorem execStmts_of_interp {fuel : Nat} {funs : FunEnv localDialect}
    {V V' : VEnv localDialect} {st st' : EvmState} {stmts : Block Op} {outcome}
    (h : Interp.execStmts localExec fuel funs V st stmts = .ok (V', st', outcome)) :
    ExecStmts localDialect funs V st stmts V' st' outcome :=
  (Interp.sound_all localExec_lawful fuel).2.2.2.1 _ _ _ _ _ _ _ h

private theorem evalBuiltin {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 st2 : EvmState} {op : Op} {args : List (Expr Op)} {values returns}
    (hargs : EvalArgs localDialect funs V st args (.vals values st1))
    (hfn : localBuiltinFn op values st1 = some (.ok returns st2)) :
    EvalExpr localDialect funs V st (.builtin op args) (.vals returns st2) :=
  Step.builtinOk hargs ((localExec_lawful op values st1 (.ok returns st2)).mpr hfn)

private def scheduleBody : Block Op := yul% {
  xSet(i, readLE32(add(msgOff, mul(i, 4))))
}

private def schedulePost : Block Op := yul% { i := add(i, 1) }

private def readLE32Decl : FDecl localDialect where
  params := ["off"]
  rets := ["v"]
  body := yul% {
    let w := mload(off)
    v := or(or(byte(0, w), shl(8, byte(1, w))),
            or(shl(16, byte(2, w)), shl(24, byte(3, w))))
  }

private def xSetDecl : FDecl localDialect where
  params := ["i", "v"]
  rets := []
  body := yul% { mstore(add(0x2a0, mul(i, 32)), and(v, 0xffffffff)) }

private def scheduleDecl : FDecl localDialect where
  params := ["msgOff"]
  rets := []
  body := yul% {
    for { let i := 0 } lt(i, 16) { i := add(i, 1) } {
      xSet(i, readLE32(add(msgOff, mul(i, 4))))
    }
  }

private theorem lookup_readLE32 :
    lookupFun verifiedFunctions "readLE32" = some (readLE32Decl, verifiedFunctions) := by
  rfl

private theorem lookup_xSet :
    lookupFun verifiedFunctions "xSet" = some (xSetDecl, verifiedFunctions) := by
  rfl

private theorem lookup_schedule :
    lookupFun verifiedFunctions "schedule" = some (scheduleDecl, verifiedFunctions) := by
  rfl

private theorem exec_readLE32Body (st : EvmState) (off : U256) :
    ExecStmt localDialect verifiedFunctions [("off", off), ("v", 0)] st
      (.block readLE32Decl.body)
      [("off", off), ("v", readLE32Value st.memory off)]
      (touchMemory st off.toNat 32) .normal := by
  apply execStmt_of_interp (fuel := 100)
  rfl

private theorem exec_xSetBody (st : EvmState) (i v : U256) :
    ExecStmt localDialect verifiedFunctions [("i", i), ("v", v)] st
      (.block xSetDecl.body) [("i", i), ("v", v)] (xSetState st i v) .normal := by
  apply execStmt_of_interp (fuel := 100)
  rfl

private theorem eval_readLE32 {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {arg : Expr Op} (off : U256)
    (hlookup : lookupFun funs "readLE32" = some (readLE32Decl, verifiedFunctions))
    (harg : EvalExpr localDialect funs V st arg (.vals [off] st1)) :
    EvalExpr localDialect funs V st (.call "readLE32" [arg])
      (.vals [readLE32Value st1.memory off] (touchMemory st1 off.toNat 32)) := by
  refine Step.callOk (D := localDialect)
    (Step.argsCons Step.argsNil harg) hlookup rfl
    (exec_readLE32Body st1 off) (Or.inl rfl)

private theorem eval_xSet {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (i v : U256)
    (hlookup : lookupFun funs "xSet" = some (xSetDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [i, v] st1)) :
    EvalExpr localDialect funs V st (.call "xSet" args)
      (.vals [] (xSetState st1 i v)) := by
  refine Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_xSetBody st1 i v) (Or.inl rfl)

private theorem eval_scheduleOffset (funs : FunEnv localDialect) (st : EvmState)
    (msgOff : U256) (i : Nat) :
    EvalExpr localDialect funs
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st
      (yulE% add(msgOff, mul(i, 4)))
      (.vals [msgOff + BitVec.ofNat 256 i * 4] st) := by
  apply evalExpr_of_interp (fuel := 20)
  rfl

private theorem eval_scheduleCond (st : EvmState) (msgOff : U256) (i : Nat) :
    EvalExpr localDialect ([] :: [] :: verifiedFunctions)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st
      (yulE% lt(i, 16))
      (.vals [if (BitVec.ofNat 256 i).toNat < 16 then (1 : U256) else (0 : U256)] st) := by
  apply Step.builtinOk (D := localDialect)
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl))
  simp [localDialect, YulSemantics.EVM.evmWithExternal,
    YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.stepOp,
    YulSemantics.EVM.bin, BitVec.ult, YulSemantics.EVM.b2w,
    YulSemantics.EVM.litValue]

private theorem exec_scheduleBody (st : EvmState) (msgOff : U256) (i : Nat) :
    ExecStmt localDialect ([] :: [] :: verifiedFunctions)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st (.block scheduleBody)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)]
      (scheduleStepState msgOff st i) .normal := by
  let bodyFuns : FunEnv localDialect := [] :: [] :: [] :: verifiedFunctions
  have hreadLookup : lookupFun bodyFuns "readLE32" =
      some (readLE32Decl, verifiedFunctions) := by
    simpa [bodyFuns, lookupFun] using lookup_readLE32
  have hxsetLookup : lookupFun bodyFuns "xSet" =
      some (xSetDecl, verifiedFunctions) := by
    simpa [bodyFuns, lookupFun] using lookup_xSet
  let off := msgOff + BitVec.ofNat 256 i * 4
  have hoff : EvalExpr localDialect bodyFuns
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st
      (yulE% add(msgOff, mul(i, 4))) (.vals [off] st) := by
    exact eval_scheduleOffset bodyFuns st msgOff i
  have hread := eval_readLE32 off hreadLookup hoff
  have hargs : EvalArgs localDialect bodyFuns
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st
      [yulE% i, yulE% readLE32(add(msgOff, mul(i, 4)))]
      (.vals [BitVec.ofNat 256 i, readLE32Value st.memory off]
        (touchMemory st off.toNat 32)) :=
    Step.argsCons (Step.argsCons Step.argsNil hread) (Step.var rfl)
  have hx := eval_xSet (BitVec.ofNat 256 i) (readLE32Value st.memory off)
    hxsetLookup hargs
  refine Step.block (D := localDialect)
    (Vb := [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)]) ?_
  exact Step.seqCons (D := localDialect)
    (Step.exprStmt (D := localDialect) hx) (Step.seqNil (D := localDialect))

private theorem exec_schedulePost (st : EvmState) (msgOff : U256) (i : Nat) :
    ExecStmt localDialect ([] :: [] :: verifiedFunctions)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st (.block schedulePost)
      [("i", BitVec.ofNat 256 i + (1 : U256)), ("msgOff", msgOff)] st .normal := by
  apply execStmt_of_interp (fuel := 30)
  rfl

private theorem exec_schedulePost_succ (st : EvmState) (msgOff : U256) (i : Nat) :
    ExecStmt localDialect ([] :: [] :: verifiedFunctions)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st (.block schedulePost)
      [("i", BitVec.ofNat 256 (i + 1)), ("msgOff", msgOff)] st .normal := by
  have heq : BitVec.ofNat 256 i + (1 : U256) = BitVec.ofNat 256 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
  have h := exec_schedulePost st msgOff i
  rw [heq] at h
  exact h

/-- The sixteen-iteration source loop stores the exact schedule-state transformer. -/
theorem eval_schedule {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {arg : Expr Op} (msgOff : U256)
    (hlookup : lookupFun funs "schedule" = some (scheduleDecl, verifiedFunctions))
    (harg : EvalExpr localDialect funs V st arg (.vals [msgOff] st1)) :
    EvalExpr localDialect funs V st (.call "schedule" [arg])
      (.vals [] (scheduleState msgOff st1)) := by
  refine Step.callOk (D := localDialect) (decl := scheduleDecl)
    (cenv := verifiedFunctions) (Vend := [("msgOff", msgOff)]) (o := .normal)
    (Step.argsCons Step.argsNil harg) hlookup rfl ?_ (Or.inl rfl)
  simp only [scheduleDecl, List.zip, List.zipWith, bindZeros, List.map,
    List.append_nil]
  refine Step.block (D := localDialect) (Vb := [("msgOff", msgOff)]) ?_
  refine Step.seqCons (D := localDialect) ?_ (Step.seqNil (D := localDialect))
  refine Step.forLoop (D := localDialect)
    (Vinit := [("i", 0), ("msgOff", msgOff)])
    (stinit := st1)
    (Vend := [("i", BitVec.ofNat 256 16), ("msgOff", msgOff)]) ?_ ?_
  · exact Step.seqCons (D := localDialect) (Step.letVal Step.lit rfl)
      (Step.seqNil (D := localDialect))
  · let Inv : Nat → VEnv localDialect → EvmState → Prop :=
      fun remaining V current => ∃ i,
        i + remaining = 16 ∧
        V = [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] ∧
        current = schedulePrefix msgOff st1 i
    let loopFuns : FunEnv localDialect :=
      hoist localDialect [Stmt.letDecl ["i"] (some (.lit (.number 0)))] ::
        hoist localDialect scheduleDecl.body :: verifiedFunctions
    have hdone : ∀ V current, Inv 0 V current →
        ∃ cv current',
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 16))
            (.vals [cv] current') ∧ cv = localDialect.zero ∧ Inv 0 V current' := by
      intro V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hi16 : i = 16 := by omega
      subst i
      refine ⟨(0 : U256), schedulePrefix msgOff st1 16, ?_, rfl, ?_⟩
      · simpa [loopFuns, scheduleDecl, hoist, BitVec.toNat_ofNat] using
          eval_scheduleCond (schedulePrefix msgOff st1 16) msgOff 16
      · exact ⟨16, by omega, rfl, rfl⟩
    have hstep : ∀ n V current, Inv (n + 1) V current →
        ∃ cv currentCond Vb currentBody ob Vp currentPost,
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 16))
            (.vals [cv] currentCond) ∧ cv ≠ localDialect.zero ∧
          ExecStmt localDialect loopFuns V currentCond (.block scheduleBody)
            Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
          ExecStmt localDialect loopFuns Vb currentBody (.block schedulePost)
            Vp currentPost .normal ∧ Inv n Vp currentPost := by
      intro n V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hilimit : i < 16 := by omega
      refine ⟨(1 : U256), schedulePrefix msgOff st1 i,
        [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)],
        schedulePrefix msgOff st1 (i + 1), .normal,
        [("i", BitVec.ofNat 256 (i + 1)), ("msgOff", msgOff)],
        schedulePrefix msgOff st1 (i + 1), ?_, by decide, ?_, Or.inl rfl, ?_, ?_⟩
      · have hlt : (BitVec.ofNat 256 i).toNat < 16 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact hilimit
        have hcond := eval_scheduleCond (schedulePrefix msgOff st1 i) msgOff i
        rw [if_pos hlt] at hcond
        simpa [loopFuns, scheduleDecl, hoist] using hcond
      · simpa [loopFuns, scheduleDecl, hoist, schedulePrefix] using
          exec_scheduleBody (schedulePrefix msgOff st1 i) msgOff i
      · simpa [loopFuns, scheduleDecl, hoist] using
          exec_schedulePost_succ (schedulePrefix msgOff st1 (i + 1)) msgOff i
      · exact ⟨i + 1, by omega, rfl, rfl⟩
    obtain ⟨V', current', hloop, hInv⟩ :=
      ExecLoop.countdown (D := localDialect) (funs := loopFuns)
        (cond := yulE% lt(i, 16)) (post := schedulePost) (body := scheduleBody)
        (Inv := Inv) hdone hstep 16
        [("i", 0), ("msgOff", msgOff)] st1 ⟨0, by omega, rfl, rfl⟩
    obtain ⟨i, hi, hV, hstate⟩ := hInv
    have hi16 : i = 16 := by omega
    subst i
    subst V'
    subst current'
    simpa [loopFuns, scheduleDecl, scheduleBody, schedulePost, hoist,
      scheduleState] using hloop

/-! ### Compression helper contracts -/

private def stAtDecl : FDecl localDialect where
  params := ["base", "i"]
  rets := ["v"]
  body := yul% { v := mload(add(base, mul(i, 32))) }

private def stSetDecl : FDecl localDialect where
  params := ["base", "i", "v"]
  rets := []
  body := yul% { mstore(add(base, mul(i, 32)), and(v, 0xffffffff)) }

private def xAtDecl : FDecl localDialect where
  params := ["i"]
  rets := ["v"]
  body := yul% { v := mload(add(0x2a0, mul(i, 32))) }

private def tableAtDecl : FDecl localDialect where
  params := ["base", "i"]
  rets := ["v"]
  body := yul% { v := byte(mod(i, 32), mload(add(base, mul(div(i, 32), 32)))) }

private def rotlDecl : FDecl localDialect where
  params := ["x", "n"]
  rets := ["r"]
  body := yul% { r := and(or(shl(n, x), shr(sub(32, n), x)), 0xffffffff) }

private def fDecl : FDecl localDialect where
  params := ["j", "x", "y", "z"]
  rets := ["v"]
  body := yul% {
    switch j
    case 0 { v := xor(xor(x, y), z) }
    case 1 { v := or(and(x, y), and(not(x), z)) }
    case 2 { v := and(xor(or(x, not(y)), z), 0xffffffff) }
    case 3 { v := or(and(x, z), and(y, not(z))) }
    default { v := and(xor(x, or(y, not(z))), 0xffffffff) }
  }

private def roundDecl : FDecl localDialect where
  params := ["base", "j", "wordIndex", "rotation", "k"]
  rets := []
  body := yul% {
    let a := stAt(base, 0)
    let b := stAt(base, 1)
    let c := stAt(base, 2)
    let d := stAt(base, 3)
    let e := stAt(base, 4)
    let t := and(add(add(add(a, f(j, b, c, d)), xAt(wordIndex)), k), 0xffffffff)
    t := and(add(rotl(t, rotation), e), 0xffffffff)
    stSet(base, 0, e)
    stSet(base, 4, d)
    stSet(base, 3, rotl(c, 10))
    stSet(base, 2, b)
    stSet(base, 1, t)
  }

private theorem lookup_stAt :
    lookupFun verifiedFunctions "stAt" = some (stAtDecl, verifiedFunctions) := by rfl
private theorem lookup_stSet :
    lookupFun verifiedFunctions "stSet" = some (stSetDecl, verifiedFunctions) := by rfl
private theorem lookup_xAt :
    lookupFun verifiedFunctions "xAt" = some (xAtDecl, verifiedFunctions) := by rfl
private theorem lookup_tableAt :
    lookupFun verifiedFunctions "tableAt" = some (tableAtDecl, verifiedFunctions) := by rfl
private theorem lookup_rotl :
    lookupFun verifiedFunctions "rotl" = some (rotlDecl, verifiedFunctions) := by rfl
private theorem lookup_f :
    lookupFun verifiedFunctions "f" = some (fDecl, verifiedFunctions) := by rfl
private theorem lookup_round :
    lookupFun verifiedFunctions "round" = some (roundDecl, verifiedFunctions) := by rfl

private def wordAddress (base i : U256) : U256 := base + i * 32

private def rotlValue (x n : U256) : U256 :=
  sourceRotl x n

private def fValue (j : Nat) (x y z : U256) : U256 :=
  sourceF j x y z

private theorem exec_stAtBody (st : EvmState) (base i : U256) :
    ExecStmt localDialect verifiedFunctions
      [("base", base), ("i", i), ("v", 0)] st (.block stAtDecl.body)
      [("base", base), ("i", i), ("v", loadWord st.memory (wordAddress base i).toNat)]
      (touchMemory st (wordAddress base i).toNat 32) .normal := by
  apply execStmt_of_interp (fuel := 80)
  rfl

private theorem exec_stSetBody (st : EvmState) (base i v : U256) :
    ExecStmt localDialect verifiedFunctions [("base", base), ("i", i), ("v", v)] st
      (.block stSetDecl.body) [("base", base), ("i", i), ("v", v)]
      (storeWordAt st (wordAddress base i) (v &&& 0xffffffff)) .normal := by
  apply execStmt_of_interp (fuel := 80)
  rfl

private theorem exec_xAtBody (st : EvmState) (i : U256) :
    ExecStmt localDialect verifiedFunctions [("i", i), ("v", 0)] st (.block xAtDecl.body)
      [("i", i), ("v", loadWord st.memory (wordAddress 0x2a0 i).toNat)]
      (touchMemory st (wordAddress 0x2a0 i).toNat 32) .normal := by
  apply execStmt_of_interp (fuel := 80)
  rfl

private theorem exec_tableAtBody (st : EvmState) (base i : U256) :
    ExecStmt localDialect verifiedFunctions
      [("base", base), ("i", i), ("v", 0)] st (.block tableAtDecl.body)
      [("base", base), ("i", i), ("v", tableValue st.memory base i)]
      (touchMemory st (base + (i / 32) * 32).toNat 32) .normal := by
  apply execStmt_of_interp (fuel := 100)
  rfl

private theorem exec_rotlBody (st : EvmState) (x n : U256) :
    ExecStmt localDialect verifiedFunctions [("x", x), ("n", n), ("r", 0)] st
      (.block rotlDecl.body) [("x", x), ("n", n), ("r", rotlValue x n)] st .normal := by
  apply execStmt_of_interp (fuel := 100)
  rfl

private theorem exec_fBody (st : EvmState) (j : Nat) (hj : j < 5) (x y z : U256) :
    ExecStmt localDialect verifiedFunctions
      [("j", BitVec.ofNat 256 j), ("x", x), ("y", y), ("z", z), ("v", 0)] st
      (.block fDecl.body)
      [("j", BitVec.ofNat 256 j), ("x", x), ("y", y), ("z", z),
        ("v", fValue j x y z)]
      st .normal := by
  interval_cases j <;> apply execStmt_of_interp (fuel := 100) <;> rfl

private theorem eval_stAt {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (base i : U256)
    (hlookup : lookupFun funs "stAt" = some (stAtDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [base, i] st1)) :
    EvalExpr localDialect funs V st (.call "stAt" args)
      (.vals [loadWord st1.memory (wordAddress base i).toNat]
        (touchMemory st1 (wordAddress base i).toNat 32)) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_stAtBody st1 base i) (Or.inl rfl)

private theorem eval_stSet {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (base i v : U256)
    (hlookup : lookupFun funs "stSet" = some (stSetDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [base, i, v] st1)) :
    EvalExpr localDialect funs V st (.call "stSet" args)
      (.vals [] (storeWordAt st1 (wordAddress base i) (v &&& 0xffffffff))) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_stSetBody st1 base i v) (Or.inl rfl)

private theorem eval_xAt {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (i : U256)
    (hlookup : lookupFun funs "xAt" = some (xAtDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [i] st1)) :
    EvalExpr localDialect funs V st (.call "xAt" args)
      (.vals [loadWord st1.memory (wordAddress 0x2a0 i).toNat]
        (touchMemory st1 (wordAddress 0x2a0 i).toNat 32)) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_xAtBody st1 i) (Or.inl rfl)

private theorem eval_tableAt {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (base i : U256)
    (hlookup : lookupFun funs "tableAt" = some (tableAtDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [base, i] st1)) :
    EvalExpr localDialect funs V st (.call "tableAt" args)
      (.vals [tableValue st1.memory base i]
        (touchMemory st1 (base + (i / 32) * 32).toNat 32)) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_tableAtBody st1 base i) (Or.inl rfl)

private theorem eval_rotl {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (x n : U256)
    (hlookup : lookupFun funs "rotl" = some (rotlDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [x, n] st1)) :
    EvalExpr localDialect funs V st (.call "rotl" args) (.vals [rotlValue x n] st1) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_rotlBody st1 x n) (Or.inl rfl)

private theorem eval_f {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (j : Nat) (hj : j < 5) (x y z : U256)
    (hlookup : lookupFun funs "f" = some (fDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args
      (.vals [BitVec.ofNat 256 j, x, y, z] st1)) :
    EvalExpr localDialect funs V st (.call "f" args)
      (.vals [fValue j x y z] st1) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_fBody st1 j hj x y z) (Or.inl rfl)

private theorem exec_roundBody (st : EvmState) (base : U256) (j : Nat) (hj : j < 5)
    (wordIndex rotation constant : U256) :
    ExecStmt localDialect verifiedFunctions
      [("base", base), ("j", BitVec.ofNat 256 j), ("wordIndex", wordIndex),
        ("rotation", rotation), ("k", constant)] st (.block roundDecl.body)
      [("base", base), ("j", BitVec.ofNat 256 j), ("wordIndex", wordIndex),
        ("rotation", rotation), ("k", constant)]
      (roundState st base j wordIndex rotation constant) .normal := by
  let funs : FunEnv localDialect := [] :: verifiedFunctions
  let V0 : VEnv localDialect :=
    [("base", base), ("j", BitVec.ofNat 256 j), ("wordIndex", wordIndex),
      ("rotation", rotation), ("k", constant)]
  let x := workingAt st.memory base
  let sA := touchMemory st (wordAddress base 0).toNat 32
  let sB := touchMemory sA (wordAddress base 1).toNat 32
  let sC := touchMemory sB (wordAddress base 2).toNat 32
  let sD := touchMemory sC (wordAddress base 3).toNat 32
  let sE := touchMemory sD (wordAddress base 4).toNat 32
  let wordAddr := wordAddress 0x2a0 wordIndex
  let word := loadWord st.memory wordAddr.toNat
  let sW := touchMemory sE wordAddr.toNat 32
  let mask : U256 := localDialect.litValue (.number 0xffffffff)
  have mask_eq : (0xffffffff : U256) = BitVec.ofNat 256 0xffffffff := by
    exact BitVec.ofNatLT_eq_ofNat _
  let t0 := (x.a + sourceF j x.b x.c x.d + word + constant) &&& mask
  let t := (sourceRotl t0 rotation + x.e) &&& mask
  let Vabcde : VEnv localDialect :=
    [("e", x.e), ("d", x.d), ("c", x.c), ("b", x.b), ("a", x.a)] ++ V0
  let Vt : VEnv localDialect := ("t", t0) :: Vabcde
  have hstAt : lookupFun funs "stAt" = some (stAtDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_stAt
  have hxAt : lookupFun funs "xAt" = some (xAtDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_xAt
  have hf : lookupFun funs "f" = some (fDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_f
  have hrotl : lookupFun funs "rotl" = some (rotlDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_rotl
  have hstSet : lookupFun funs "stSet" = some (stSetDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_stSet
  have callStAt (V : VEnv localDialect) (current : EvmState) (i : Nat)
      (hbase : VEnv.get V "base" = some base) :
      EvalExpr localDialect funs V current
        (.call "stAt" [.var "base", .lit (.number i)])
        (.vals [loadWord current.memory (wordAddress base (BitVec.ofNat 256 i)).toNat]
          (touchMemory current (wordAddress base (BitVec.ofNat 256 i)).toNat 32)) := by
    apply eval_stAt base (BitVec.ofNat 256 i) hstAt
    exact Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hbase)
  have ha : EvalExpr localDialect funs V0 st (yulE% stAt(base, 0)) (.vals [x.a] sA) := by
    simpa [x, sA, workingAt, wordAddress, V0, mkCall, parse, touchMemory] using
      callStAt V0 st 0 rfl
  have hb : EvalExpr localDialect funs (("a", x.a) :: V0) sA
      (yulE% stAt(base, 1)) (.vals [x.b] sB) := by
    simpa [x, sA, sB, workingAt, wordAddress, V0, mkCall, parse, touchMemory] using
      callStAt (("a", x.a) :: V0) sA 1 rfl
  have hc : EvalExpr localDialect funs (("b", x.b) :: ("a", x.a) :: V0) sB
      (yulE% stAt(base, 2)) (.vals [x.c] sC) := by
    simpa [x, sA, sB, sC, workingAt, wordAddress, V0, mkCall, parse, touchMemory] using
      callStAt (("b", x.b) :: ("a", x.a) :: V0) sB 2 rfl
  have hd : EvalExpr localDialect funs
      (("c", x.c) :: ("b", x.b) :: ("a", x.a) :: V0) sC
      (yulE% stAt(base, 3)) (.vals [x.d] sD) := by
    simpa [x, sA, sB, sC, sD, workingAt, wordAddress, V0, mkCall, parse,
      touchMemory] using
      callStAt (("c", x.c) :: ("b", x.b) :: ("a", x.a) :: V0) sC 3 rfl
  have he : EvalExpr localDialect funs
      (("d", x.d) :: ("c", x.c) :: ("b", x.b) :: ("a", x.a) :: V0) sD
      (yulE% stAt(base, 4)) (.vals [x.e] sE) := by
    simpa [x, sA, sB, sC, sD, sE, workingAt, wordAddress, V0, mkCall, parse,
      touchMemory] using
      callStAt (("d", x.d) :: ("c", x.c) :: ("b", x.b) :: ("a", x.a) :: V0) sD 4 rfl
  have hxcall : EvalExpr localDialect funs Vabcde sE (yulE% xAt(wordIndex))
      (.vals [word] sW) := by
    have hargs : EvalArgs localDialect funs Vabcde sE [.var "wordIndex"]
        (.vals [wordIndex] sE) := Step.argsCons Step.argsNil (Step.var rfl)
    have h := eval_xAt wordIndex hxAt hargs
    simpa [mkCall, parse, word, wordAddr, sW, sA, sB, sC, sD, sE,
      touchMemory, wordAddress] using h
  have hfcall : EvalExpr localDialect funs Vabcde sW (yulE% f(j, b, c, d))
      (.vals [sourceF j x.b x.c x.d] sW) := by
    have hargs : EvalArgs localDialect funs Vabcde sW
        [.var "j", .var "b", .var "c", .var "d"]
        (.vals [BitVec.ofNat 256 j, x.b, x.c, x.d] sW) := Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl))
        (Step.var rfl)) (Step.var rfl)) (Step.var rfl)
    have h := eval_f j hj x.b x.c x.d hf hargs
    simpa [mkCall, parse, fValue] using h
  have ht0expr : EvalExpr localDialect funs Vabcde sE
      (yulE% and(add(add(add(a, f(j, b, c, d)), xAt(wordIndex)), k), 0xffffffff))
      (.vals [t0] sW) := by
    have haf : EvalExpr localDialect funs Vabcde sW
        (yulE% add(a, f(j, b, c, d)))
        (.vals [x.a + sourceF j x.b x.c x.d] sW) := by
      exact evalBuiltin
        (Step.argsCons (Step.argsCons Step.argsNil hfcall) (Step.var rfl)) rfl
    have hax : EvalExpr localDialect funs Vabcde sE
        (yulE% add(add(a, f(j, b, c, d)), xAt(wordIndex)))
        (.vals [x.a + sourceF j x.b x.c x.d + word] sW) := by
      exact evalBuiltin
        (Step.argsCons (Step.argsCons Step.argsNil hxcall) haf) rfl
    have hak : EvalExpr localDialect funs Vabcde sE
        (yulE% add(add(add(a, f(j, b, c, d)), xAt(wordIndex)), k))
        (.vals [x.a + sourceF j x.b x.c x.d + word + constant] sW) := by
      exact evalBuiltin
        (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) hax) rfl
    have hmask : EvalExpr localDialect funs Vabcde sE
        (yulE% and(add(add(add(a, f(j, b, c, d)), xAt(wordIndex)), k), 0xffffffff))
        (.vals [(x.a + sourceF j x.b x.c x.d + word + constant) &&& 0xffffffff]
          sW) := by
      exact evalBuiltin
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hak) rfl
    simpa [t0, mask, fValue, rotlValue, mask_eq, localDialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.litValue] using hmask
  have hrotlcall : EvalExpr localDialect funs Vt sW (yulE% rotl(t, rotation))
      (.vals [sourceRotl t0 rotation] sW) := by
    have hargs : EvalArgs localDialect funs Vt sW [.var "t", .var "rotation"]
        (.vals [t0, rotation] sW) :=
      Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)
    have h := eval_rotl t0 rotation hrotl hargs
    simpa [mkCall, parse, rotlValue] using h
  have htexpr : EvalExpr localDialect funs Vt sW
      (yulE% and(add(rotl(t, rotation), e), 0xffffffff)) (.vals [t] sW) := by
    have hadd : EvalExpr localDialect funs Vt sW
        (yulE% add(rotl(t, rotation), e))
        (.vals [sourceRotl t0 rotation + x.e] sW) := by
      exact evalBuiltin
        (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) hrotlcall) rfl
    have hmask : EvalExpr localDialect funs Vt sW
        (yulE% and(add(rotl(t, rotation), e), 0xffffffff))
        (.vals [(sourceRotl t0 rotation + x.e) &&& 0xffffffff] sW) := by
      exact evalBuiltin
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hadd) rfl
    simpa [t, mask, mask_eq, localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue] using hmask
  let r := sourceRound x j word rotation constant
  let s0 := storeWordAt sW (wordAddress base 0) (r.a &&& 0xffffffff)
  let s1 := storeWordAt s0 (wordAddress base 4) (r.e &&& 0xffffffff)
  let s2 := storeWordAt s1 (wordAddress base 3) (r.d &&& 0xffffffff)
  let s3 := storeWordAt s2 (wordAddress base 2) (r.c &&& 0xffffffff)
  let s4 := storeWordAt s3 (wordAddress base 1) (r.b &&& 0xffffffff)
  -- The five writes are assembled explicitly below; their arguments are pure and evaluated
  -- right-to-left by `Step.argsCons`.
  have hs0 : EvalExpr localDialect funs (("t", t) :: Vabcde) sW
      (yulE% stSet(base, 0, e)) (.vals [] s0) := by
    apply eval_stSet base 0 x.e hstSet
    exact Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit) (Step.var rfl)
  have hs1 : EvalExpr localDialect funs (("t", t) :: Vabcde) s0
      (yulE% stSet(base, 4, d)) (.vals [] s1) := by
    apply eval_stSet base 4 x.d hstSet
    exact Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit) (Step.var rfl)
  have hrotl10 : EvalExpr localDialect funs (("t", t) :: Vabcde) s1
      (yulE% rotl(c, 10)) (.vals [sourceRotl x.c 10] s1) := by
    apply eval_rotl x.c 10 hrotl
    exact Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)
  have hs2 : EvalExpr localDialect funs (("t", t) :: Vabcde) s1
      (yulE% stSet(base, 3, rotl(c, 10))) (.vals [] s2) := by
    apply eval_stSet base 3 (sourceRotl x.c 10) hstSet
    exact Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil hrotl10) Step.lit) (Step.var rfl)
  have hs3 : EvalExpr localDialect funs (("t", t) :: Vabcde) s2
      (yulE% stSet(base, 2, b)) (.vals [] s3) := by
    apply eval_stSet base 2 x.b hstSet
    exact Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit) (Step.var rfl)
  have hs4 : EvalExpr localDialect funs (("t", t) :: Vabcde) s3
      (yulE% stSet(base, 1, t)) (.vals [] s4) := by
    apply eval_stSet base 1 t hstSet
    exact Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit) (Step.var rfl)
  refine Step.block (D := localDialect) (Vb := ("t", t) :: Vabcde) ?_
  refine Step.seqCons (Step.letVal ha rfl) ?_
  refine Step.seqCons (Step.letVal hb rfl) ?_
  refine Step.seqCons (Step.letVal hc rfl) ?_
  refine Step.seqCons (Step.letVal hd rfl) ?_
  refine Step.seqCons (Step.letVal he rfl) ?_
  refine Step.seqCons (Step.letVal ht0expr rfl) ?_
  refine Step.seqCons (Step.assignVal htexpr rfl) ?_
  refine Step.seqCons (Step.exprStmt hs0) ?_
  refine Step.seqCons (Step.exprStmt hs1) ?_
  refine Step.seqCons (Step.exprStmt hs2) ?_
  refine Step.seqCons (Step.exprStmt hs3) ?_
  refine Step.seqCons (Step.exprStmt hs4) Step.seqNil

private theorem eval_round {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (base : U256) (j : Nat) (hj : j < 5)
    (wordIndex rotation constant : U256)
    (hlookup : lookupFun funs "round" = some (roundDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args
      (.vals [base, BitVec.ofNat 256 j, wordIndex, rotation, constant] st1)) :
    EvalExpr localDialect funs V st (.call "round" args)
      (.vals [] (roundState st1 base j wordIndex rotation constant)) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_roundBody st1 base j hj wordIndex rotation constant) (Or.inl rfl)

private def leftRoundBody : Block Op := yul% {
  let j := div(i, 16)
  round(0x0c0, j, tableAt(0x4a0, i), tableAt(0x560, i),
        mload(add(0x620, mul(j, 32))))
}

private def roundPost : Block Op := yul% { i := add(i, 1) }

private theorem exec_leftRoundBody (st : EvmState) (msgOff : U256) (i : Nat)
    (hi : i < 80) :
    ExecStmt localDialect ([] :: [] :: verifiedFunctions)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st (.block leftRoundBody)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)]
      (leftRoundStepState st i) .normal := by
  let funs : FunEnv localDialect := [] :: [] :: [] :: verifiedFunctions
  let iw : U256 := BitVec.ofNat 256 i
  let j := i / 16
  let jw : U256 := BitVec.ofNat 256 j
  let V0 : VEnv localDialect := [("i", iw), ("msgOff", msgOff)]
  let Vj : VEnv localDialect := ("j", jw) :: V0
  let kAddr : U256 := 0x620 + jw * 32
  let sK := touchMemory st kAddr.toNat 32
  let constant := loadWord st.memory kAddr.toNat
  let sR := touchMemory sK (0x560 + (iw / 32) * 32).toNat 32
  let rotation := tableValue st.memory 0x560 iw
  let sW := touchMemory sR (0x4a0 + (iw / 32) * 32).toNat 32
  let wordIndex := tableValue st.memory 0x4a0 iw
  have hjlt : j < 5 := by omega
  have htable : lookupFun funs "tableAt" =
      some (tableAtDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_tableAt
  have hround : lookupFun funs "round" = some (roundDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_round
  have hjexpr : EvalExpr localDialect funs V0 st (yulE% div(i, 16))
      (.vals [jw] st) := by
    have hraw : Interp.evalExpr localExec 20 funs V0 st (yulE% div(i, 16)) =
        .ok (.vals [iw / (16 : U256)] st) := by rfl
    have hdiv : iw / (16 : U256) = jw := by
      apply BitVec.eq_of_toNat_eq
      change i % 2 ^ 256 / 16 = i / 16 % 2 ^ 256
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hdiv] at hraw
    exact evalExpr_of_interp hraw
  have hk : EvalExpr localDialect funs Vj st
      (yulE% mload(add(0x620, mul(j, 32)))) (.vals [constant] sK) := by
    apply evalExpr_of_interp (fuel := 40)
    rfl
  have hrot : EvalExpr localDialect funs Vj sK (yulE% tableAt(0x560, i))
      (.vals [rotation] sR) := by
    have hargs : EvalArgs localDialect funs Vj sK
        [yulE% 0x560, yulE% i] (.vals [(0x560 : U256), iw] sK) :=
      Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit
    have h := eval_tableAt 0x560 iw htable hargs
    have hmem : sK.memory = st.memory := by rfl
    rw [hmem] at h
    simpa [rotation, sR, Vj, V0, iw, mkCall, parse] using h
  have hword : EvalExpr localDialect funs Vj sR (yulE% tableAt(0x4a0, i))
      (.vals [wordIndex] sW) := by
    have hargs : EvalArgs localDialect funs Vj sR
        [yulE% 0x4a0, yulE% i] (.vals [(0x4a0 : U256), iw] sR) :=
      Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit
    have h := eval_tableAt 0x4a0 iw htable hargs
    have hmem : sR.memory = st.memory := by rfl
    rw [hmem] at h
    simpa [wordIndex, sW, Vj, V0, iw, mkCall, parse] using h
  have hargs : EvalArgs localDialect funs Vj st
      [yulE% 0x0c0, yulE% j, yulE% tableAt(0x4a0, i),
        yulE% tableAt(0x560, i), yulE% mload(add(0x620, mul(j, 32)))]
      (.vals [(0x0c0 : U256), jw, wordIndex, rotation, constant] sW) :=
    Step.argsCons
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons (Step.argsCons Step.argsNil hk) hrot) hword)
        (Step.var rfl)) Step.lit
  have hcall := eval_round 0x0c0 j hjlt wordIndex rotation constant hround hargs
  refine Step.block (D := localDialect) (Vb := Vj) ?_
  refine Step.seqCons (D := localDialect) (Step.letVal hjexpr rfl) ?_
  refine Step.seqCons (D := localDialect) (Step.exprStmt hcall) ?_
  simpa [funs, leftRoundBody, hoist, leftRoundStepState, V0, Vj, iw, jw, j,
    kAddr, sK, constant, sR,
    rotation, sW, wordIndex] using (Step.seqNil (D := localDialect)
      (funs := funs) (V := Vj) (st := roundState sW 0x0c0 j wordIndex rotation constant))

private theorem exec_roundPost_succ (funs : FunEnv localDialect)
    (Vtail : VEnv localDialect) (st : EvmState) (i : Nat) :
    ExecStmt localDialect funs (("i", BitVec.ofNat 256 i) :: Vtail) st
      (.block roundPost) (("i", BitVec.ofNat 256 (i + 1)) :: Vtail) st .normal := by
  let innerFuns : FunEnv localDialect := hoist localDialect roundPost :: funs
  have hi : BitVec.ofNat 256 i + localDialect.litValue (.number 1) =
      BitVec.ofNat 256 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue]
  have hadd : EvalExpr localDialect innerFuns
      (("i", BitVec.ofNat 256 i) :: Vtail) st (yulE% add(i, 1))
      (.vals [BitVec.ofNat 256 (i + 1)] st) := by
    have hargs : EvalArgs localDialect innerFuns
        (("i", BitVec.ofNat 256 i) :: Vtail) st [yulE% i, yulE% 1]
        (.vals [BitVec.ofNat 256 i, localDialect.litValue (.number 1)] st) :=
      Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)
    have hfn : localBuiltinFn .add
        [BitVec.ofNat 256 i, localDialect.litValue (.number 1)] st =
        some (.ok
          [BitVec.ofNat 256 i + localDialect.litValue (.number 1)] st) := by
      rfl
    have hraw := evalBuiltin hargs hfn
    rw [hi] at hraw
    simpa [mkCall, parse] using hraw
  have hseq : Step localDialect innerFuns
      (("i", BitVec.ofNat 256 i) :: Vtail) st (.stmts roundPost)
      (.sres (("i", BitVec.ofNat 256 (i + 1)) :: Vtail) st .normal) := by
    have hassign := Step.assignVal (D := localDialect) (vars := ["i"]) hadd rfl
    have hset : VEnv.setMany (("i", BitVec.ofNat 256 i) :: Vtail)
        ["i"] [BitVec.ofNat 256 (i + 1)] =
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail := by rfl
    rw [hset] at hassign
    simpa [roundPost] using
      (Step.seqCons (D := localDialect) hassign (Step.seqNil (D := localDialect)))
  have hblock := Step.block (D := localDialect) hseq
  simpa [innerFuns, roundPost, restore] using hblock

private theorem eval_roundCond (funs : FunEnv localDialect) (Vtail : VEnv localDialect)
    (st : EvmState) (i : Nat) (hi : i ≤ 80) :
    EvalExpr localDialect funs (("i", BitVec.ofNat 256 i) :: Vtail) st
      (yulE% lt(i, 80))
      (.vals [if i < 80 then (1 : U256) else (0 : U256)] st) := by
  apply Step.builtinOk (D := localDialect)
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl))
  simp [localDialect, YulSemantics.EVM.evmWithExternal,
    YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.stepOp,
    YulSemantics.EVM.bin, BitVec.ult, YulSemantics.EVM.b2w,
    YulSemantics.EVM.litValue]
  change (if i % 2 ^ 256 < 80 then (1 : U256) else 0) =
    if i < 80 then 1 else 0
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]

private def leftRoundFor : Stmt Op :=
  .forLoop [Stmt.letDecl ["i"] (some (.lit (.number 0)))]
    (yulE% lt(i, 80)) roundPost leftRoundBody

private theorem exec_leftRoundFor (st : EvmState) (msgOff : U256) :
    ExecStmt localDialect ([] :: verifiedFunctions) [("msgOff", msgOff)] st
      leftRoundFor [("msgOff", msgOff)] (leftRoundPrefix 80 st) .normal := by
  let loopFuns : FunEnv localDialect := [] :: [] :: verifiedFunctions
  refine Step.forLoop (D := localDialect)
    (Vinit := [("i", 0), ("msgOff", msgOff)])
    (stinit := st)
    (Vend := [("i", BitVec.ofNat 256 80), ("msgOff", msgOff)]) ?_ ?_
  · exact Step.seqCons (D := localDialect) (Step.letVal Step.lit rfl)
      (Step.seqNil (D := localDialect))
  · let Inv : Nat → VEnv localDialect → EvmState → Prop :=
      fun remaining V current => ∃ i,
        i + remaining = 80 ∧
        V = [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] ∧
        current = leftRoundPrefix i st
    have hdone : ∀ V current, Inv 0 V current →
        ∃ cv current',
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 80))
            (.vals [cv] current') ∧ cv = localDialect.zero ∧ Inv 0 V current' := by
      intro V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hi80 : i = 80 := by omega
      subst i
      refine ⟨(0 : U256), leftRoundPrefix 80 st, ?_, rfl, ?_⟩
      · simpa [loopFuns] using
          eval_roundCond loopFuns [("msgOff", msgOff)] (leftRoundPrefix 80 st) 80
            (by omega)
      · exact ⟨80, by omega, rfl, rfl⟩
    have hstep : ∀ n V current, Inv (n + 1) V current →
        ∃ cv currentCond Vb currentBody ob Vp currentPost,
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 80))
            (.vals [cv] currentCond) ∧ cv ≠ localDialect.zero ∧
          ExecStmt localDialect loopFuns V currentCond (.block leftRoundBody)
            Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
          ExecStmt localDialect loopFuns Vb currentBody (.block roundPost)
            Vp currentPost .normal ∧ Inv n Vp currentPost := by
      intro n V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hilimit : i < 80 := by omega
      refine ⟨(1 : U256), leftRoundPrefix i st,
        [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)],
        leftRoundPrefix (i + 1) st, .normal,
        [("i", BitVec.ofNat 256 (i + 1)), ("msgOff", msgOff)],
        leftRoundPrefix (i + 1) st, ?_, by decide, ?_, Or.inl rfl, ?_, ?_⟩
      · have hcond := eval_roundCond loopFuns [("msgOff", msgOff)]
          (leftRoundPrefix i st) i (by omega)
        rw [if_pos hilimit] at hcond
        exact hcond
      · simpa [leftRoundPrefix] using
          exec_leftRoundBody (leftRoundPrefix i st) msgOff i hilimit
      · exact exec_roundPost_succ loopFuns [("msgOff", msgOff)]
          (leftRoundPrefix (i + 1) st) i
      · exact ⟨i + 1, by omega, rfl, rfl⟩
    obtain ⟨V', current', hloop, hInv⟩ :=
      ExecLoop.countdown (D := localDialect) (funs := loopFuns)
        (cond := yulE% lt(i, 80)) (post := roundPost) (body := leftRoundBody)
        (Inv := Inv) hdone hstep 80
        [("i", 0), ("msgOff", msgOff)] st ⟨0, by omega, rfl, rfl⟩
    obtain ⟨i, hi, hV, hstate⟩ := hInv
    have hi80 : i = 80 := by omega
    subst i
    subst V'
    subst current'
    simpa [leftRoundFor, leftRoundBody, roundPost, loopFuns, hoist] using hloop

private theorem exec_fixed80For (body : Block Op) (states : Nat → EvmState)
    (st : EvmState) (msgOff : U256) (hprefix : states 0 = st)
    (hbody : ∀ i, i < 80 →
      ExecStmt localDialect ([] :: [] :: verifiedFunctions)
        [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] (states i) (.block body)
        [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] (states (i + 1)) .normal) :
    ExecStmt localDialect ([] :: verifiedFunctions) [("msgOff", msgOff)] st
      (.forLoop [Stmt.letDecl ["i"] (some (.lit (.number 0)))]
        (yulE% lt(i, 80)) roundPost body)
      [("msgOff", msgOff)] (states 80) .normal := by
  let loopFuns : FunEnv localDialect := [] :: [] :: verifiedFunctions
  refine Step.forLoop (D := localDialect)
    (Vinit := [("i", 0), ("msgOff", msgOff)])
    (stinit := st)
    (Vend := [("i", BitVec.ofNat 256 80), ("msgOff", msgOff)]) ?_ ?_
  · exact Step.seqCons (D := localDialect) (Step.letVal Step.lit rfl)
      (Step.seqNil (D := localDialect))
  · let Inv : Nat → VEnv localDialect → EvmState → Prop :=
      fun remaining V current => ∃ i,
        i + remaining = 80 ∧
        V = [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] ∧ current = states i
    have hdone : ∀ V current, Inv 0 V current →
        ∃ cv current',
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 80))
            (.vals [cv] current') ∧ cv = localDialect.zero ∧ Inv 0 V current' := by
      intro V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hi80 : i = 80 := by omega
      subst i
      refine ⟨(0 : U256), states 80, ?_, rfl, ⟨80, by omega, rfl, rfl⟩⟩
      simpa [loopFuns] using
        eval_roundCond loopFuns [("msgOff", msgOff)] (states 80) 80 (by omega)
    have hstep : ∀ n V current, Inv (n + 1) V current →
        ∃ cv currentCond Vb currentBody ob Vp currentPost,
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 80))
            (.vals [cv] currentCond) ∧ cv ≠ localDialect.zero ∧
          ExecStmt localDialect loopFuns V currentCond (.block body)
            Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
          ExecStmt localDialect loopFuns Vb currentBody (.block roundPost)
            Vp currentPost .normal ∧ Inv n Vp currentPost := by
      intro n V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hilimit : i < 80 := by omega
      refine ⟨(1 : U256), states i,
        [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)], states (i + 1), .normal,
        [("i", BitVec.ofNat 256 (i + 1)), ("msgOff", msgOff)], states (i + 1),
        ?_, by decide, hbody i hilimit, Or.inl rfl, ?_, ?_⟩
      · have hcond := eval_roundCond loopFuns [("msgOff", msgOff)]
          (states i) i (by omega)
        rw [if_pos hilimit] at hcond
        exact hcond
      · exact exec_roundPost_succ loopFuns [("msgOff", msgOff)] (states (i + 1)) i
      · exact ⟨i + 1, by omega, rfl, rfl⟩
    obtain ⟨V', current', hloop, hInv⟩ :=
      ExecLoop.countdown (D := localDialect) (funs := loopFuns)
        (cond := yulE% lt(i, 80)) (post := roundPost) (body := body)
        (Inv := Inv) hdone hstep 80
        [("i", 0), ("msgOff", msgOff)] st ⟨0, by omega, rfl, hprefix.symm⟩
    obtain ⟨i, hi, hV, hstate⟩ := hInv
    have hi80 : i = 80 := by omega
    subst i
    subst V'
    subst current'
    simpa [loopFuns, hoist] using hloop

private def rightRoundBody : Block Op := yul% {
  let j := div(i, 16)
  round(0x160, sub(4, j), tableAt(0x500, i), tableAt(0x5c0, i),
        mload(add(0x6c0, mul(j, 32))))
}

private def rightRoundFor : Stmt Op :=
  .forLoop [Stmt.letDecl ["i"] (some (.lit (.number 0)))]
    (yulE% lt(i, 80)) roundPost rightRoundBody

private theorem exec_rightRoundBody (st : EvmState) (msgOff : U256) (i : Nat)
    (hi : i < 80) :
    ExecStmt localDialect ([] :: [] :: verifiedFunctions)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)] st (.block rightRoundBody)
      [("i", BitVec.ofNat 256 i), ("msgOff", msgOff)]
      (rightRoundStepState st i) .normal := by
  let funs : FunEnv localDialect := [] :: [] :: [] :: verifiedFunctions
  let iw : U256 := BitVec.ofNat 256 i
  let group := i / 16
  let groupWord : U256 := BitVec.ofNat 256 group
  let j := 4 - group
  let jWord : U256 := BitVec.ofNat 256 j
  let V0 : VEnv localDialect := [("i", iw), ("msgOff", msgOff)]
  let Vg : VEnv localDialect := ("j", groupWord) :: V0
  let kAddr : U256 := 0x6c0 + groupWord * 32
  let sK := touchMemory st kAddr.toNat 32
  let constant := loadWord st.memory kAddr.toNat
  let sR := touchMemory sK (0x5c0 + (iw / 32) * 32).toNat 32
  let rotation := tableValue st.memory 0x5c0 iw
  let sW := touchMemory sR (0x500 + (iw / 32) * 32).toNat 32
  let wordIndex := tableValue st.memory 0x500 iw
  have hgroup : group ≤ 4 := by omega
  have hjlt : j < 5 := by omega
  have htable : lookupFun funs "tableAt" =
      some (tableAtDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_tableAt
  have hround : lookupFun funs "round" = some (roundDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_round
  have hgexpr : EvalExpr localDialect funs V0 st (yulE% div(i, 16))
      (.vals [groupWord] st) := by
    have hraw : Interp.evalExpr localExec 20 funs V0 st (yulE% div(i, 16)) =
        .ok (.vals [iw / (16 : U256)] st) := by rfl
    have hdiv : iw / (16 : U256) = groupWord := by
      apply BitVec.eq_of_toNat_eq
      change i % 2 ^ 256 / 16 = i / 16 % 2 ^ 256
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hdiv] at hraw
    exact evalExpr_of_interp hraw
  have hk : EvalExpr localDialect funs Vg st
      (yulE% mload(add(0x6c0, mul(j, 32)))) (.vals [constant] sK) := by
    apply evalExpr_of_interp (fuel := 40)
    rfl
  have hrot : EvalExpr localDialect funs Vg sK (yulE% tableAt(0x5c0, i))
      (.vals [rotation] sR) := by
    have hargs : EvalArgs localDialect funs Vg sK
        [yulE% 0x5c0, yulE% i] (.vals [(0x5c0 : U256), iw] sK) :=
      Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit
    have h := eval_tableAt 0x5c0 iw htable hargs
    have hmem : sK.memory = st.memory := by rfl
    rw [hmem] at h
    simpa [rotation, sR, Vg, V0, iw, mkCall, parse] using h
  have hword : EvalExpr localDialect funs Vg sR (yulE% tableAt(0x500, i))
      (.vals [wordIndex] sW) := by
    have hargs : EvalArgs localDialect funs Vg sR
        [yulE% 0x500, yulE% i] (.vals [(0x500 : U256), iw] sR) :=
      Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit
    have h := eval_tableAt 0x500 iw htable hargs
    have hmem : sR.memory = st.memory := by rfl
    rw [hmem] at h
    simpa [wordIndex, sW, Vg, V0, iw, mkCall, parse] using h
  have hjexpr : EvalExpr localDialect funs Vg sW (yulE% sub(4, j))
      (.vals [jWord] sW) := by
    have hraw : Interp.evalExpr localExec 20 funs Vg sW (yulE% sub(4, j)) =
        .ok (.vals [(4 : U256) - groupWord] sW) := by rfl
    have hsub : (4 : U256) - groupWord = jWord := by
      have hgNat : groupWord.toNat = group := by
        change group % 2 ^ 256 = group
        rw [Nat.mod_eq_of_lt (by omega)]
      have hle : groupWord ≤ (4 : U256) := by
        rw [BitVec.le_def, hgNat]
        change group ≤ 4
        exact hgroup
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le hle, hgNat]
      change 4 - group = (4 - group) % 2 ^ 256
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hraw
    exact evalExpr_of_interp hraw
  have hargs : EvalArgs localDialect funs Vg st
      [yulE% 0x160, yulE% sub(4, j), yulE% tableAt(0x500, i),
        yulE% tableAt(0x5c0, i), yulE% mload(add(0x6c0, mul(j, 32)))]
      (.vals [(0x160 : U256), jWord, wordIndex, rotation, constant] sW) :=
    Step.argsCons
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons (Step.argsCons Step.argsNil hk) hrot) hword)
        hjexpr) Step.lit
  have hcall := eval_round 0x160 j hjlt wordIndex rotation constant hround hargs
  refine Step.block (D := localDialect) (Vb := Vg) ?_
  refine Step.seqCons (D := localDialect) (Step.letVal hgexpr rfl) ?_
  refine Step.seqCons (D := localDialect) (Step.exprStmt hcall) ?_
  simpa [funs, rightRoundBody, hoist, rightRoundStepState, V0, Vg, iw,
    groupWord, jWord, group, j, kAddr, sK, constant, sR, rotation, sW,
    wordIndex] using (Step.seqNil (D := localDialect) (funs := funs) (V := Vg)
      (st := roundState sW 0x160 j wordIndex rotation constant))

private theorem exec_rightRoundFor (st : EvmState) (msgOff : U256) :
    ExecStmt localDialect ([] :: verifiedFunctions) [("msgOff", msgOff)] st
      rightRoundFor [("msgOff", msgOff)] (rightRoundPrefix 80 st) .normal := by
  simpa [rightRoundFor] using
    exec_fixed80For rightRoundBody (fun i => rightRoundPrefix i st) st msgOff rfl
      (fun i hi => by
        simpa [rightRoundPrefix] using exec_rightRoundBody (rightRoundPrefix i st) msgOff i hi)

private def compressionTail : Block Op := yul% {
  let t := and(add(add(mload(0x220), mload(0x100)), mload(0x1c0)), 0xffffffff)
  hSet(1, and(add(add(mload(0x240), mload(0x120)), mload(0x1e0)), 0xffffffff))
  hSet(2, and(add(add(mload(0x260), mload(0x140)), mload(0x160)), 0xffffffff))
  hSet(3, and(add(add(mload(0x280), mload(0x0c0)), mload(0x180)), 0xffffffff))
  hSet(4, and(add(add(mload(0x200), mload(0x0e0)), mload(0x1a0)), 0xffffffff))
  hSet(0, t)
}

private def compressDecl : FDecl localDialect where
  params := ["msgOff"]
  rets := []
  body := yul% {
    schedule(msgOff)
    mcopy(0x0c0, 0x020, 0x0a0)
    mcopy(0x160, 0x020, 0x0a0)
    mcopy(0x200, 0x020, 0x0a0)
    for { let i := 0 } lt(i, 80) { i := add(i, 1) } {
      let j := div(i, 16)
      round(0x0c0, j, tableAt(0x4a0, i), tableAt(0x560, i),
            mload(add(0x620, mul(j, 32))))
    }
    for { let i := 0 } lt(i, 80) { i := add(i, 1) } {
      let j := div(i, 16)
      round(0x160, sub(4, j), tableAt(0x500, i), tableAt(0x5c0, i),
            mload(add(0x6c0, mul(j, 32))))
    }
    let t := and(add(add(mload(0x220), mload(0x100)), mload(0x1c0)), 0xffffffff)
    hSet(1, and(add(add(mload(0x240), mload(0x120)), mload(0x1e0)), 0xffffffff))
    hSet(2, and(add(add(mload(0x260), mload(0x140)), mload(0x160)), 0xffffffff))
    hSet(3, and(add(add(mload(0x280), mload(0x0c0)), mload(0x180)), 0xffffffff))
    hSet(4, and(add(add(mload(0x200), mload(0x0e0)), mload(0x1a0)), 0xffffffff))
    hSet(0, t)
  }

private theorem lookup_compress :
    lookupFun verifiedFunctions "compress" = some (compressDecl, verifiedFunctions) := by rfl

private theorem mcopyLiteral (funs : FunEnv localDialect) (V : VEnv localDialect)
    (st : EvmState) (dst src n : Nat) :
    EvalExpr localDialect funs V st
      (.builtin .mcopy [.lit (.number dst), .lit (.number src), .lit (.number n)])
      (.vals [] (mcopyState st (litValue (.number dst)) (litValue (.number src))
        (litValue (.number n)))) := by
  exact Step.builtinOk
    (Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) Step.lit) rfl

private def hSetDecl : FDecl localDialect where
  params := ["i", "v"]
  rets := []
  body := yul% { mstore(add(0x20, mul(i, 32)), and(v, 0xffffffff)) }

private theorem lookup_hSet :
    lookupFun verifiedFunctions "hSet" = some (hSetDecl, verifiedFunctions) := by rfl

private theorem exec_hSetBody (st : EvmState) (i v : U256) :
    ExecStmt localDialect verifiedFunctions [("i", i), ("v", v)] st
      (.block hSetDecl.body) [("i", i), ("v", v)] (hSetState st i v) .normal := by
  apply execStmt_of_interp (fuel := 80)
  rfl

private theorem eval_hSet {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (i v : U256)
    (hlookup : lookupFun funs "hSet" = some (hSetDecl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [i, v] st1)) :
    EvalExpr localDialect funs V st (.call "hSet" args)
      (.vals [] (hSetState st1 i v)) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_hSetBody st1 i v) (Or.inl rfl)

private theorem eval_addThreeMasked (funs : FunEnv localDialect)
    (V : VEnv localDialect) (st : EvmState) (p q r : Nat) :
    EvalExpr localDialect funs V st
      (.builtin .and [
        .builtin .add [
          .builtin .add [.builtin .mload [.lit (.number p)],
            .builtin .mload [.lit (.number q)]],
          .builtin .mload [.lit (.number r)]],
        .lit (.number 0xffffffff)])
      (.vals [(addThreeMasked st (litValue (.number p)) (litValue (.number q))
        (litValue (.number r))).1]
        (addThreeMasked st (litValue (.number p)) (litValue (.number q))
          (litValue (.number r))).2) := by
  apply evalExpr_of_interp (fuel := 100)
  rfl

private theorem exec_compressionTail (st : EvmState) (msgOff : U256) :
    ExecStmts localDialect ([] :: verifiedFunctions) [("msgOff", msgOff)] st
      compressionTail
      (("t", (addThreeMasked st 0x220 0x100 0x1c0).1) :: [("msgOff", msgOff)])
      (compressionTailState st) .normal := by
  let funs : FunEnv localDialect := [] :: verifiedFunctions
  let V : VEnv localDialect := [("msgOff", msgOff)]
  let tPair := addThreeMasked st 0x220 0x100 0x1c0
  let Vt : VEnv localDialect := ("t", tPair.1) :: V
  let p1 := addThreeMasked tPair.2 0x240 0x120 0x1e0
  let s1 := hSetState p1.2 1 p1.1
  let p2 := addThreeMasked s1 0x260 0x140 0x160
  let s2 := hSetState p2.2 2 p2.1
  let p3 := addThreeMasked s2 0x280 0x0c0 0x180
  let s3 := hSetState p3.2 3 p3.1
  let p4 := addThreeMasked s3 0x200 0x0e0 0x1a0
  let s4 := hSetState p4.2 4 p4.1
  have hlookup : lookupFun funs "hSet" = some (hSetDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_hSet
  have ht : EvalExpr localDialect funs V st
      (yulE% and(add(add(mload(0x220), mload(0x100)), mload(0x1c0)), 0xffffffff))
      (.vals [tPair.1] tPair.2) := by
    simpa [tPair, mkCall, parse, localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue, BitVec.ofNatLT_eq_ofNat] using
      eval_addThreeMasked funs V st 0x220 0x100 0x1c0
  have callComputed (current : EvmState) (i : Nat) (p q r : Nat) :
      let pair := addThreeMasked current (litValue (.number p))
        (litValue (.number q)) (litValue (.number r))
      EvalExpr localDialect funs Vt current
        (.call "hSet" [.lit (.number i),
          .builtin .and [
            .builtin .add [
              .builtin .add [.builtin .mload [.lit (.number p)],
                .builtin .mload [.lit (.number q)]],
              .builtin .mload [.lit (.number r)]],
            .lit (.number 0xffffffff)]])
        (.vals [] (hSetState pair.2 (litValue (.number i)) pair.1)) := by
    dsimp only
    apply eval_hSet (litValue (.number i))
      (addThreeMasked current (litValue (.number p)) (litValue (.number q))
        (litValue (.number r))).1 hlookup
    exact Step.argsCons
      (Step.argsCons Step.argsNil (eval_addThreeMasked funs Vt current p q r)) Step.lit
  have h1 := callComputed tPair.2 1 0x240 0x120 0x1e0
  have h2 := callComputed s1 2 0x260 0x140 0x160
  have h3 := callComputed s2 3 0x280 0x0c0 0x180
  have h4 := callComputed s3 4 0x200 0x0e0 0x1a0
  have h0 : EvalExpr localDialect funs Vt s4 (yulE% hSet(0, t))
      (.vals [] (hSetState s4 0 tPair.1)) := by
    apply eval_hSet 0 tPair.1 hlookup
    exact Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit
  refine Step.seqCons (Step.letVal ht rfl) ?_
  refine Step.seqCons (Step.exprStmt (by
    simpa [funs, V, Vt, p1, s1, tPair, mkCall, parse, localDialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.litValue,
      BitVec.ofNatLT_eq_ofNat] using h1)) ?_
  refine Step.seqCons (Step.exprStmt (by
    simpa [funs, V, Vt, tPair, p1, s1, p2, s2, mkCall, parse, localDialect,
      YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue, BitVec.ofNatLT_eq_ofNat] using h2)) ?_
  refine Step.seqCons (Step.exprStmt (by
    simpa [funs, V, Vt, tPair, p1, s1, p2, s2, p3, s3, mkCall, parse,
      localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue, BitVec.ofNatLT_eq_ofNat] using h3)) ?_
  refine Step.seqCons (Step.exprStmt (by
    simpa [funs, V, Vt, tPair, p1, s1, p2, s2, p3, s3, p4, s4, mkCall,
      parse, localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue, BitVec.ofNatLT_eq_ofNat] using h4)) ?_
  refine Step.seqCons (Step.exprStmt h0) ?_
  simpa [compressionTailState, V, Vt, tPair, p1, s1, p2, s2, p3, s3, p4, s4]
    using (Step.seqNil (D := localDialect) (funs := funs) (V := Vt)
      (st := hSetState s4 0 tPair.1))

private theorem exec_compressBody (st : EvmState) (msgOff : U256) :
    ExecStmt localDialect verifiedFunctions [("msgOff", msgOff)] st
      (.block compressDecl.body) [("msgOff", msgOff)] (compressionState st msgOff)
      .normal := by
  let funs : FunEnv localDialect := [] :: verifiedFunctions
  let V : VEnv localDialect := [("msgOff", msgOff)]
  let s0 := scheduleState msgOff st
  let s1 := mcopyState s0 0x0c0 0x020 0x0a0
  let s2 := mcopyState s1 0x160 0x020 0x0a0
  let s3 := mcopyState s2 0x200 0x020 0x0a0
  let s4 := leftRoundPrefix 80 s3
  let s5 := rightRoundPrefix 80 s4
  have hscheduleLookup : lookupFun funs "schedule" =
      some (scheduleDecl, verifiedFunctions) := by
    simpa [funs, lookupFun] using lookup_schedule
  have hschedule : EvalExpr localDialect funs V st (yulE% schedule(msgOff))
      (.vals [] s0) := by
    have hvar : EvalExpr localDialect funs V st (.var "msgOff")
        (.vals [msgOff] st) := Step.var (by rfl)
    have h := eval_schedule msgOff hscheduleLookup hvar
    simpa [s0, mkCall, parse] using h
  have hm1 := mcopyLiteral funs V s0 0x0c0 0x020 0x0a0
  have hm2 := mcopyLiteral funs V s1 0x160 0x020 0x0a0
  have hm3 := mcopyLiteral funs V s2 0x200 0x020 0x0a0
  have hl := exec_leftRoundFor s3 msgOff
  have hr := exec_rightRoundFor s4 msgOff
  have ht := exec_compressionTail s5 msgOff
  refine Step.block (D := localDialect)
    (Vb := ("t", (addThreeMasked s5 0x220 0x100 0x1c0).1) :: V) ?_
  change ExecStmts localDialect funs V st compressDecl.body
    (("t", (addThreeMasked s5 0x220 0x100 0x1c0).1) :: V)
    (compressionState st msgOff) .normal
  refine Step.seqCons (Step.exprStmt hschedule) ?_
  refine Step.seqCons (Step.exprStmt (by
    simpa [s1, localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue, BitVec.ofNatLT_eq_ofNat, mkCall, parse] using hm1)) ?_
  refine Step.seqCons (Step.exprStmt (by
    simpa [s1, s2, localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue, BitVec.ofNatLT_eq_ofNat, mkCall, parse] using hm2)) ?_
  refine Step.seqCons (Step.exprStmt (by
    simpa [s0, s1, s2, s3, localDialect, YulSemantics.EVM.evmWithExternal,
      YulSemantics.EVM.litValue, BitVec.ofNatLT_eq_ofNat, mkCall, parse] using hm3)) ?_
  refine Step.seqCons (by
    simpa [funs, V, s0, s1, s2, s3, leftRoundFor, leftRoundBody, roundPost,
      localDialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.litValue,
      BitVec.ofNatLT_eq_ofNat] using hl) ?_
  refine Step.seqCons (by
    simpa [funs, V, s0, s1, s2, s3, s4, rightRoundFor, rightRoundBody,
      roundPost, localDialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.litValue,
      BitVec.ofNatLT_eq_ofNat] using hr) ?_
  simpa [funs, V, s0, s1, s2, s3, s4, s5, compressDecl, compressionTail,
    compressionState, compressionWorkState] using ht

/-- Exact source-level execution contract for one complete compression call. -/
theorem eval_compress {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {arg : Expr Op} (msgOff : U256)
    (hlookup : lookupFun funs "compress" = some (compressDecl, verifiedFunctions))
    (harg : EvalExpr localDialect funs V st arg (.vals [msgOff] st1)) :
    EvalExpr localDialect funs V st (.call "compress" [arg])
      (.vals [] (compressionState st1 msgOff)) := by
  exact Step.callOk (D := localDialect) (Step.argsCons Step.argsNil harg) hlookup rfl
    (exec_compressBody st1 msgOff) (Or.inl rfl)

private def initTablesDecl : FDecl localDialect where
  params := []
  rets := []
  body := yul% {
    mstore(0x4a0, 0x000102030405060708090a0b0c0d0e0f07040d010a060f030c000905020e0b08)
    mstore(0x4c0, 0x030a0e04090f0801020700060d0b050c01090b0a00080c040d03070f0e050602)
    mstore(0x4e0, 0x04000509070c020a0e0103080b060f0d00000000000000000000000000000000)
    mstore(0x500, 0x050e070009020b040d060f08010a030c060b0307000d050a0e0f080c04090102)
    mstore(0x520, 0x0f050103070e06090b080c020a00040d08060401030b0f00050c020d09070a0e)
    mstore(0x540, 0x0c0f0a040105080706020d0e0003090b00000000000000000000000000000000)
    mstore(0x560, 0x0b0e0f0c050807090b0d0e0f060709080706080d0b09070f070c0f090b070d0c)
    mstore(0x580, 0x0b0d06070e090d0f0e080d06050c07050b0c0e0f0e0f0908090e05060806050c)
    mstore(0x5a0, 0x090f050b06080d0c050c0d0e0b08050600000000000000000000000000000000)
    mstore(0x5c0, 0x0809090b0d0f0f050707080b0e0e0c06090d0f070c08090b07070c07060f0d0b)
    mstore(0x5e0, 0x09070f0b0806060e0c0d050e0d0d07050f05080b0e0e060e06090c090c050f08)
    mstore(0x600, 0x08050c090c050e06080d06050f0d0b0b00000000000000000000000000000000)
    mstore(0x620, 0x00000000)
    mstore(0x640, 0x5a827999)
    mstore(0x660, 0x6ed9eba1)
    mstore(0x680, 0x8f1bbcdc)
    mstore(0x6a0, 0xa953fd4e)
    mstore(0x6c0, 0x50a28be6)
    mstore(0x6e0, 0x5c4dd124)
    mstore(0x700, 0x6d703ef3)
    mstore(0x720, 0x7a6d76e9)
    mstore(0x740, 0x00000000)
  }

private theorem lookup_initTables :
    lookupFun verifiedFunctions "initTables" =
      some (initTablesDecl, verifiedFunctions) := by
  rfl

private theorem mstoreLiteral (funs : FunEnv localDialect) (V : VEnv localDialect)
    (st : EvmState) (p v : Nat) :
    EvalExpr localDialect funs V st
      (.builtin .mstore [.lit (.number p), .lit (.number v)])
      (.vals [] (storeWordAt st (litValue (.number p)) (litValue (.number v)))) := by
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl

/-- Exact leaf execution for the fixed table initializer. The complete state is named only here;
clients use `initTables_mem` below. -/
theorem eval_initTables (st : EvmState) :
    EvalExpr localDialect verifiedFunctions [] st (.call "initTables" [])
      (.vals [] (initTablesState st)) := by
  refine Step.callOk (D := localDialect) (decl := initTablesDecl)
    (cenv := verifiedFunctions) (Vend := []) (o := .normal)
    Step.argsNil lookup_initTables rfl ?_ (Or.inl rfl)
  simp only [initTablesDecl, List.zip, List.zipWith, bindZeros, List.map, List.nil_append]
  refine Step.block (Vb := []) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ st 0x4a0
    0x000102030405060708090a0b0c0d0e0f07040d010a060f030c000905020e0b08)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x4c0
    0x030a0e04090f0801020700060d0b050c01090b0a00080c040d03070f0e050602)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x4e0
    0x04000509070c020a0e0103080b060f0d00000000000000000000000000000000)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x500
    0x050e070009020b040d060f08010a030c060b0307000d050a0e0f080c04090102)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x520
    0x0f050103070e06090b080c020a00040d08060401030b0f00050c020d09070a0e)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x540
    0x0c0f0a040105080706020d0e0003090b00000000000000000000000000000000)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x560
    0x0b0e0f0c050807090b0d0e0f060709080706080d0b09070f070c0f090b070d0c)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x580
    0x0b0d06070e090d0f0e080d06050c07050b0c0e0f0e0f0908090e05060806050c)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x5a0
    0x090f050b06080d0c050c0d0e0b08050600000000000000000000000000000000)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x5c0
    0x0809090b0d0f0f050707080b0e0e0c06090d0f070c08090b07070c07060f0d0b)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x5e0
    0x09070f0b0806060e0c0d050e0d0d07050f05080b0e0e060e06090c090c050f08)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x600
    0x08050c090c050e06080d06050f0d0b0b00000000000000000000000000000000)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x620 0x00000000)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x640 0x5a827999)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x660 0x6ed9eba1)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x680 0x8f1bbcdc)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x6a0 0xa953fd4e)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x6c0 0x50a28be6)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x6e0 0x5c4dd124)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x700 0x6d703ef3)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x720 0x7a6d76e9)) ?_
  refine Step.seqCons (Step.exprStmt (mstoreLiteral _ _ _ 0x740 0x00000000)) ?_
  exact Step.seqNil

private def initHDecl : FDecl localDialect where
  params := []
  rets := []
  body := yul% {
    hSet(0, 0x67452301)
    hSet(1, 0xefcdab89)
    hSet(2, 0x98badcfe)
    hSet(3, 0x10325476)
    hSet(4, 0xc3d2e1f0)
  }

private theorem lookup_initH :
    lookupFun verifiedFunctions "initH" = some (initHDecl, verifiedFunctions) := by rfl

/-- Exact source-level execution of the five-word RIPEMD initial state. -/
theorem eval_initHCall (st : EvmState) :
    EvalExpr localDialect verifiedFunctions [] st (.call "initH" [])
      (.vals [] (initHState st)) := by
  exact evalExpr_of_interp (Interpreter.eval_initH 0 st)

end Challenge.Ripemd160.Reference.Proofs.Yul.Procedures
