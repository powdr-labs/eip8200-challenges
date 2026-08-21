import Challenge.Ripemd160.Reference.Proofs.Yul.Driver
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Exact execution of the RIPEMD-160 Yul driver

The algorithmic loop invariant lives in `Driver`.  This module gives compact
exact state transformers for padding, block iteration, digest serialization,
and the top-level Yul block.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Yul.Execution

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open Interpreter
open Procedures
open Algorithm
open Driver
open Challenge.Ripemd160.Reference.Proofs.Bytecode

def paddedLengthValue (st : EvmState) : U256 :=
  ((BitVec.ofNat 256 st.env.calldata.length + 72) / 64) * 64

def calldataCopyState (st : EvmState) : EvmState :=
  let n := (BitVec.ofNat 256 st.env.calldata.length).toNat
  { touchMemory st 0x800 n with
    memory := copyInto st.memory 0x800 0 n st.env.calldata }

def sentinelState (st : EvmState) : EvmState :=
  let p := (0x800 + BitVec.ofNat 256 st.env.calldata.length : U256)
  { touchMemory (calldataCopyState st) p.toNat 1 with
    memory := storeByte (calldataCopyState st).memory p.toNat 0x80 }

def lengthOffset (st : EvmState) : U256 :=
  0x800 + (paddedLengthValue st - 8)

def lengthStepState (original : EvmState) (st : EvmState) (i : Nat) : EvmState :=
  let bitLength := BitVec.ofNat 256 original.env.calldata.length * 8
  let value := (bitLength >>> (8 * i)) &&& 0xff
  let p := lengthOffset original + BitVec.ofNat 256 i
  { touchMemory st p.toNat 1 with memory := storeByte st.memory p.toNat value }

def lengthPrefix (original : EvmState) : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st => lengthStepState original (lengthPrefix original i st) i

def padState (st : EvmState) : EvmState :=
  lengthPrefix st 8 (sentinelState st)

def padLoopTail (st : EvmState) : VEnv localDialect :=
  let n : U256 := BitVec.ofNat 256 st.env.calldata.length
  [("lenOff", lengthOffset st), ("bitLen", n * 8), ("n", n),
    ("paddedLen", paddedLengthValue st)]

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

private theorem evalBuiltin {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 st2 : EvmState} {op : Op} {args : List (Expr Op)} {values returns}
    (hargs : EvalArgs localDialect funs V st args (.vals values st1))
    (hfn : localBuiltinFn op values st1 = some (.ok returns st2)) :
    EvalExpr localDialect funs V st (.builtin op args) (.vals returns st2) :=
  Step.builtinOk hargs ((localExec_lawful op values st1 (.ok returns st2)).mpr hfn)

private def padBody : Block Op := yul% {
  mstore8(add(lenOff, i), and(shr(mul(8, i), bitLen), 0xff))
}

private def padPost : Block Op := yul% { i := add(i, 1) }

private def padDecl : FDecl localDialect where
  params := []
  rets := ["paddedLen"]
  body := yul% {
    let n := calldatasize()
    paddedLen := mul(div(add(n, 72), 64), 64)
    calldatacopy(0x800, 0, n)
    mstore8(add(0x800, n), 0x80)
    let bitLen := mul(n, 8)
    let lenOff := add(0x800, sub(paddedLen, 8))
    for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
      mstore8(add(lenOff, i), and(shr(mul(8, i), bitLen), 0xff))
    }
  }

private theorem lookup_pad :
    lookupFun verifiedFunctions "pad" = some (padDecl, verifiedFunctions) := by
  rfl

private theorem eval_padCond (funs : FunEnv localDialect) (Vtail : VEnv localDialect)
    (st : EvmState) (i : Nat) (hi : i ≤ 8) :
    EvalExpr localDialect funs (("i", BitVec.ofNat 256 i) :: Vtail) st (yulE% lt(i, 8))
      (.vals [if i < 8 then (1 : U256) else 0] st) := by
  apply evalExpr_of_interp (fuel := 20)
  interval_cases i <;> rfl

private theorem exec_padBody (funs : FunEnv localDialect) (original current : EvmState)
    (i : Nat) (hi : i ≤ 8) :
    ExecStmt localDialect funs (("i", BitVec.ofNat 256 i) :: padLoopTail original)
      current (.block padBody) (("i", BitVec.ofNat 256 i) :: padLoopTail original)
      (lengthStepState original current i) .normal := by
  apply execStmt_of_interp (fuel := 100)
  interval_cases i <;> rfl

private theorem exec_padPost (funs : FunEnv localDialect) (st : EvmState)
    (Vtail : VEnv localDialect) (i : Nat) (_hi : i < 8) :
    ExecStmt localDialect funs (("i", BitVec.ofNat 256 i) :: Vtail) st
      (.block padPost) (("i", BitVec.ofNat 256 (i + 1)) :: Vtail) st .normal := by
  let innerFuns : FunEnv localDialect := hoist localDialect padPost :: funs
  have hi' : BitVec.ofNat 256 i + localDialect.litValue (.number 1) =
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
        some (.ok [BitVec.ofNat 256 i + localDialect.litValue (.number 1)] st) := by
      rfl
    have hraw := evalBuiltin hargs hfn
    rw [hi'] at hraw
    simpa [mkCall, parse] using hraw
  have hseq : Step localDialect innerFuns
      (("i", BitVec.ofNat 256 i) :: Vtail) st (.stmts padPost)
      (.sres (("i", BitVec.ofNat 256 (i + 1)) :: Vtail) st .normal) := by
    have hassign := Step.assignVal (D := localDialect) (vars := ["i"]) hadd rfl
    have hset : VEnv.setMany (("i", BitVec.ofNat 256 i) :: Vtail)
        ["i"] [BitVec.ofNat 256 (i + 1)] =
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail := by rfl
    rw [hset] at hassign
    simpa [padPost] using
      (Step.seqCons (D := localDialect) hassign (Step.seqNil (D := localDialect)))
  have hblock := Step.block (D := localDialect) hseq
  simpa [innerFuns, padPost, restore] using hblock

/-- Exact source-level execution of `pad`; the fixed eight-iteration loop is
proved with the generic countdown invariant rather than interpreter unrolling. -/
theorem eval_pad (st : EvmState) :
    EvalExpr localDialect verifiedFunctions [] st (.call "pad" [])
      (.vals [paddedLengthValue st] (padState st)) := by
  let n : U256 := BitVec.ofNat 256 st.env.calldata.length
  let paddedLen := paddedLengthValue st
  let bitLen := n * 8
  let lenOff := lengthOffset st
  let Vtail : VEnv localDialect := padLoopTail st
  let bodyFuns : FunEnv localDialect := [] :: verifiedFunctions
  let loopFuns : FunEnv localDialect := [] :: bodyFuns
  have hLetN : ExecStmt localDialect bodyFuns [("paddedLen", 0)] st
      padDecl.body[0]! [("n", n), ("paddedLen", 0)] st .normal := by
    apply execStmt_of_interp (fuel := 30)
    rfl
  have hPaddedLen : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", 0)] st
      padDecl.body[1]! [("n", n), ("paddedLen", paddedLen)] st .normal := by
    apply execStmt_of_interp (fuel := 50)
    rfl
  have hCopy : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", paddedLen)] st
      padDecl.body[2]! [("n", n), ("paddedLen", paddedLen)] (calldataCopyState st) .normal := by
    apply execStmt_of_interp (fuel := 80)
    rfl
  have hSentinel : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", paddedLen)]
      (calldataCopyState st) padDecl.body[3]! [("n", n), ("paddedLen", paddedLen)]
      (sentinelState st) .normal := by
    apply execStmt_of_interp (fuel := 60)
    rfl
  have hBitLen : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", paddedLen)]
      (sentinelState st) padDecl.body[4]!
      [("bitLen", bitLen), ("n", n), ("paddedLen", paddedLen)]
      (sentinelState st) .normal := by
    apply execStmt_of_interp (fuel := 40)
    rfl
  have hLenOff : ExecStmt localDialect bodyFuns
      [("bitLen", bitLen), ("n", n), ("paddedLen", paddedLen)] (sentinelState st)
      padDecl.body[5]! Vtail (sentinelState st) .normal := by
    apply execStmt_of_interp (fuel := 50)
    rfl
  refine Step.callOk (D := localDialect) (decl := padDecl)
    (cenv := verifiedFunctions) (Vend := [("paddedLen", paddedLen)]) (o := .normal)
    Step.argsNil lookup_pad rfl ?_ (Or.inl rfl)
  simp only [padDecl, List.zip, List.zipWith, bindZeros, List.map,
    List.nil_append]
  refine Step.block (D := localDialect) (Vb := Vtail) ?_
  refine Step.seqCons (D := localDialect) hLetN ?_
  refine Step.seqCons (D := localDialect) hPaddedLen ?_
  refine Step.seqCons (D := localDialect) hCopy ?_
  refine Step.seqCons (D := localDialect) hSentinel ?_
  refine Step.seqCons (D := localDialect) hBitLen ?_
  refine Step.seqCons (D := localDialect) hLenOff ?_
  refine Step.seqCons (D := localDialect) ?_ Step.seqNil
  refine Step.forLoop (D := localDialect)
    (Vinit := ("i", 0) :: Vtail) (stinit := sentinelState st)
    (Vend := ("i", BitVec.ofNat 256 8) :: Vtail) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · let Inv : Nat → VEnv localDialect → EvmState → Prop :=
      fun remaining V current => ∃ i,
        i + remaining = 8 ∧ V = ("i", BitVec.ofNat 256 i) :: Vtail ∧
          current = lengthPrefix st i (sentinelState st)
    have hdone : ∀ V current, Inv 0 V current →
        ∃ cv current', EvalExpr localDialect loopFuns V current (yulE% lt(i, 8))
          (.vals [cv] current') ∧ cv = 0 ∧ Inv 0 V current' := by
      intro V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have : i = 8 := by omega
      subst i
      exact ⟨0, _, eval_padCond loopFuns Vtail _ 8 (by omega), rfl, 8, by omega,
        rfl, rfl⟩
    have hstep : ∀ remaining V current, Inv (remaining + 1) V current →
        ∃ cv currentCond Vb currentBody ob Vp currentPost,
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 8))
            (.vals [cv] currentCond) ∧ cv ≠ 0 ∧
          ExecStmt localDialect loopFuns V currentCond (.block padBody)
            Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
          ExecStmt localDialect loopFuns Vb currentBody (.block padPost)
            Vp currentPost .normal ∧ Inv remaining Vp currentPost := by
      intro remaining V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hi8 : i < 8 := by omega
      refine ⟨(1 : U256), lengthPrefix st i (sentinelState st),
        ("i", BitVec.ofNat 256 i) :: Vtail,
        lengthPrefix st (i + 1) (sentinelState st), .normal,
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail,
        lengthPrefix st (i + 1) (sentinelState st), ?_, by decide, ?_,
        Or.inl rfl, ?_, ?_⟩
      · simpa [hi8] using eval_padCond loopFuns Vtail _ i (by omega)
      · simpa [lengthPrefix] using
          exec_padBody loopFuns st (lengthPrefix st i (sentinelState st)) i (by omega)
      · exact exec_padPost loopFuns _ Vtail i hi8
      · exact ⟨i + 1, by omega, rfl, rfl⟩
    obtain ⟨V', current', hloop, hInv⟩ :=
      ExecLoop.countdown (D := localDialect) (funs := loopFuns)
        (cond := yulE% lt(i, 8)) (post := padPost) (body := padBody)
        (Inv := Inv) hdone hstep 8 (("i", 0) :: Vtail) (sentinelState st)
        ⟨0, by omega, rfl, rfl⟩
    obtain ⟨i, hi, hV, hstate⟩ := hInv
    have : i = 8 := by omega
    subst i
    subst V'
    subst current'
    simpa [loopFuns, bodyFuns, padBody, padPost, Vtail, padState, padDecl,
      hoist] using hloop

/-! ## Padding abstraction -/

theorem calldataSize_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (BitVec.ofNat 256 input.size).toNat = input.size := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans hfit (by norm_num)

theorem paddedLengthValue_eq (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input) :
    paddedLengthValue st = BitVec.ofNat 256 (Padding.paddedLength input.size) := by
  apply BitVec.eq_of_toNat_eq
  simp only [paddedLengthValue, hcd, YulEvmCompiler.ByteArray.toList_eq_data,
    Array.length_toList,
    BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_ofNat]
  change ((((input.size % 2 ^ 256 + 72) % 2 ^ 256) / 64 * 64) % 2 ^ 256) =
    Padding.paddedLength input.size % 2 ^ 256
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num) : input.size < 2 ^ 256)]
  norm_num only [Nat.reduceMod, Nat.reducePow]
  have hsum : input.size + 72 < 2 ^ 256 := by
    have := hfit
    unfold CalldataFits at this
    norm_num at this ⊢
    omega
  norm_num only [Nat.reducePow] at hsum ⊢
  rw [Nat.mod_eq_of_lt hsum]
  change Padding.paddedLength input.size % 2 ^ 256 =
    Padding.paddedLength input.size % 2 ^ 256
  rfl

theorem lengthOffset_toNat (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input) :
    (lengthOffset st).toNat =
      0x800 + Padding.paddedLength input.size - 8 := by
  rw [lengthOffset, paddedLengthValue_eq st input hcd hfit]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  change (2048 + ((2 ^ 256 - 8 +
    Padding.paddedLength input.size % 2 ^ 256) % 2 ^ 256)) % 2 ^ 256 =
      2048 + Padding.paddedLength input.size - 8
  have hpaddedPos := Padding.paddedLength_pos input.size
  have hpadded : Padding.paddedLength input.size < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    have := hfit
    unfold CalldataFits at this
    norm_num at this ⊢
    omega
  rw [Nat.mod_eq_of_lt hpadded]
  have hpadded8 : 8 ≤ Padding.paddedLength input.size := by
    have := Padding.input_and_footer_fit input.size
    omega
  have hsub : (Padding.paddedLength input.size + 2 ^ 256 - 8) % 2 ^ 256 =
      Padding.paddedLength input.size - 8 := by
    have heq : Padding.paddedLength input.size + 2 ^ 256 - 8 =
        (Padding.paddedLength input.size - 8) + 2 ^ 256 := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.add_zero]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.add_comm (2 ^ 256 - 8), ← Nat.add_sub_assoc (by omega : 8 ≤ 2 ^ 256),
    hsub]
  have hlt := Padding.paddedLength_lt input.size
  have := hfit
  unfold CalldataFits at this
  have hbound : 2048 + (Padding.paddedLength input.size - 8) < 2 ^ 256 := by
    norm_num at this ⊢
    omega
  rw [Nat.mod_eq_of_lt hbound]
  omega

theorem lengthAddress_toNat (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
    (lengthOffset st + BitVec.ofNat 256 i).toNat =
      0x800 + Padding.paddedLength input.size - 8 + i := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [lengthOffset_toNat st input hcd hfit,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 256), Nat.mod_eq_of_lt]
  have hlt := Padding.paddedLength_lt input.size
  have := hfit
  unfold CalldataFits at this
  norm_num at this ⊢
  omega

theorem lengthValue_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    byteAt (((BitVec.ofNat 256 input.size * 8) >>> (8 * i)) &&& 0xff) 0 =
      (Padding.lengthBytes input)[i]?.getD 0 := by
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _
    (by simpa using hi : i < (Padding.lengthBytes input).size)]
  rw [Padding.lengthByte input i hi]
  unfold byteAt
  congr 1
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, BitVec.toNat_ofNat]
  change ((((input.size % 2 ^ 256 * 8) % 2 ^ 256) >>> (8 * i) &&& 255) >>> 0) =
    input.size * 8 / 2 ^ (8 * i) % 256
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hbits : input.size * 8 < 2 ^ 256 := by
    have := hfit
    unfold CalldataFits at this
    norm_num at this ⊢
    omega
  rw [Nat.mod_eq_of_lt hsize, Nat.mod_eq_of_lt hbits]
  rw [Nat.shiftRight_zero]
  rw [show 255 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  congr 1
  rw [Nat.shiftRight_eq_div_pow]

theorem lengthPrefix_hit (original base : EvmState) (input : ByteArray)
    (hcd : original.env.calldata = input.toList) (hfit : CalldataFits input)
    (n : Nat) (hn : n ≤ 8) (j : Nat) (hj : j < n) :
    (lengthPrefix original n base).memory
        (0x800 + Padding.paddedLength input.size - 8 + j) =
      (Padding.lengthBytes input)[j]?.getD 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [lengthPrefix]
      unfold lengthStepState
      simp only
      rw [lengthAddress_toNat original input hcd hfit n (by omega)]
      unfold storeByte
      by_cases hjn : j = n
      · subst j
        rw [if_pos rfl]
        simpa [hcd, YulEvmCompiler.ByteArray.toList_eq_data,
          Array.length_toList] using lengthValue_eq input hfit n (by omega)
      · rw [if_neg (by omega)]
        exact ih (by omega) (by omega)

theorem lengthPrefix_outside (original base : EvmState) (input : ByteArray)
    (hcd : original.env.calldata = input.toList) (hfit : CalldataFits input)
    (n : Nat) (hn : n ≤ 8) (p : Nat)
    (hout : ∀ i, i < n → p ≠ 0x800 + Padding.paddedLength input.size - 8 + i) :
    (lengthPrefix original n base).memory p = base.memory p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lengthPrefix]
      unfold lengthStepState
      simp only
      rw [lengthAddress_toNat original input hcd hfit n (by omega)]
      unfold storeByte
      rw [if_neg (hout n (by omega))]
      exact ih (by omega) (fun i hi => hout i (by omega))

private theorem calldataEnd_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (0x800 + BitVec.ofNat 256 input.size : U256).toNat = 0x800 + input.size := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  change (2048 + input.size % 2 ^ 256) % 2 ^ 256 = 2048 + input.size
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num)), Nat.mod_eq_of_lt]
  have := hfit
  unfold CalldataFits at this
  norm_num at this ⊢
  omega

theorem padState_input (st : EvmState) (input : ByteArray)
    (_hmem : st.memory = fun _ => 0) (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) (k : Nat) (hk : k < input.size) :
    (padState st).memory (0x800 + k) = input[k]?.getD 0 := by
  rw [padState, lengthPrefix_outside st (sentinelState st) input hcd hfit 8
    (by omega) (0x800 + k) (by
      intro i hi
      have hfooter := Padding.input_and_footer_fit input.size
      omega)]
  unfold sentinelState
  simp only
  rw [hcd]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  rw [show input.data.size = input.size by rfl, calldataEnd_toNat input hfit]
  unfold storeByte
  rw [if_neg (by omega)]
  unfold calldataCopyState copyInto
  simp only
  rw [hcd]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  rw [show input.data.size = input.size by rfl]
  rw [calldataSize_toNat input hfit]
  rw [if_pos (by omega)]
  unfold byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have hm := Challenge.EvmProof.Bytes.memMatch_toList input k
  unfold byteFrom at hm
  rw [YulEvmCompiler.ByteArray.toList_eq_data,
    List.getD_eq_getElem?_getD, Array.getElem?_toList] at hm
  simpa [Nat.add_sub_cancel_left, hk] using hm

theorem padState_sentinel (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input) :
    (padState st).memory (0x800 + input.size) = 0x80 := by
  rw [padState, lengthPrefix_outside st (sentinelState st) input hcd hfit 8
    (by omega) (0x800 + input.size) (by
      intro i hi
      have hfooter := Padding.input_and_footer_fit input.size
      omega)]
  unfold sentinelState
  simp only
  rw [hcd]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  rw [show input.data.size = input.size by rfl, calldataEnd_toNat input hfit]
  unfold storeByte
  rw [if_pos rfl]
  rfl

theorem padState_zero (st : EvmState) (input : ByteArray)
    (hmem : st.memory = fun _ => 0) (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) (k : Nat) (hlo : input.size < k)
    (hhi : k < Padding.paddedLength input.size - 8) :
    (padState st).memory (0x800 + k) = 0 := by
  rw [padState, lengthPrefix_outside st (sentinelState st) input hcd hfit 8
    (by omega) (0x800 + k) (by intro i hi; omega)]
  unfold sentinelState
  simp only
  rw [hcd]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  rw [show input.data.size = input.size by rfl, calldataEnd_toNat input hfit]
  unfold storeByte
  rw [if_neg (by omega)]
  unfold calldataCopyState copyInto
  simp only
  rw [hcd]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  rw [show input.data.size = input.size by rfl]
  rw [calldataSize_toNat input hfit]
  rw [if_neg (by omega)]
  rw [hmem]

theorem padState_footer (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input)
    (j : Nat) (hj : j < 8) :
    (padState st).memory
        (0x800 + (Padding.paddedLength input.size - 8 + j)) =
      (Padding.lengthBytes input)[j]?.getD 0 := by
  unfold padState
  have hfooter := Padding.input_and_footer_fit input.size
  have haddr : 0x800 + (Padding.paddedLength input.size - 8 + j) =
      0x800 + Padding.paddedLength input.size - 8 + j := by omega
  rw [haddr]
  exact lengthPrefix_hit st (sentinelState st) input hcd hfit 8 (by omega) j hj

private theorem paddedMessage_input (input : ByteArray) (k : Nat)
    (hk : k < input.size) :
    (Padding.paddedMessage input)[k]?.getD 0 = input[k]?.getD 0 := by
  simp only [Padding.paddedMessage]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
    simp only [ByteArray.size_append, Padding.zeroBytes_size,
      show (ByteArray.mk #[0x80]).size = 1 by rfl]
    omega)]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
    simp only [ByteArray.size_append, show (ByteArray.mk #[0x80]).size = 1 by rfl]
    omega)]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos hk]

private theorem paddedMessage_sentinel (input : ByteArray) :
    (Padding.paddedMessage input)[input.size]?.getD 0 = 0x80 := by
  simp only [Padding.paddedMessage]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
    simp only [ByteArray.size_append, Padding.zeroBytes_size,
      show (ByteArray.mk #[0x80]).size = 1 by rfl]
    omega)]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
    simp only [ByteArray.size_append, show (ByteArray.mk #[0x80]).size = 1 by rfl]
    omega)]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_neg (by omega)]
  rw [Nat.sub_self]
  rfl

private theorem zeroBytes_getD (n i : Nat) (hi : i < Padding.zeroCount n) :
    (Padding.zeroBytes n)[i]?.getD 0 = 0 := by
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
    simpa using hi : i < (Padding.zeroBytes n).size)]
  simp [Padding.zeroBytes, ByteArray.getElem_eq_data_getElem,
    Array.getElem_replicate]

private theorem paddedMessage_zero (input : ByteArray) (k : Nat)
    (hlo : input.size < k)
    (hhi : k < Padding.paddedLength input.size - 8) :
    (Padding.paddedMessage input)[k]?.getD 0 = 0 := by
  simp only [Padding.paddedMessage]
  have hfooter := Padding.input_and_footer_fit input.size
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
    simp only [ByteArray.size_append, Padding.zeroBytes_size,
      show (ByteArray.mk #[0x80]).size = 1 by rfl]
    rw [Padding.prefix_size]
    omega)]
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_neg (by
    simp only [ByteArray.size_append, show (ByteArray.mk #[0x80]).size = 1 by rfl]
    omega)]
  have hprefix := Padding.prefix_size input.size
  have hpair : (input ++ ByteArray.mk #[0x80]).size = input.size + 1 := by
    rw [ByteArray.size_append]
    rfl
  rw [hpair]
  apply zeroBytes_getD
  omega

private theorem paddedMessage_footer (input : ByteArray) (j : Nat) (hj : j < 8) :
    (Padding.paddedMessage input)[Padding.paddedLength input.size - 8 + j]?.getD 0 =
      (Padding.lengthBytes input)[j]?.getD 0 := by
  simp only [Padding.paddedMessage]
  have hprefix :
      ((input ++ ByteArray.mk #[0x80]) ++ Padding.zeroBytes input.size).size =
        Padding.paddedLength input.size - 8 := by
    simp only [ByteArray.size_append, Padding.zeroBytes_size,
      show (ByteArray.mk #[0x80]).size = 1 by rfl]
    exact Padding.prefix_size input.size
  rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_neg (by
    rw [hprefix]
    omega)]
  congr 1
  rw [hprefix]
  rw [Nat.add_sub_cancel_left]

/-- The exact Yul padding state contains the canonical RIPEMD padded message. -/
theorem padState_padded (st : EvmState) (input : ByteArray)
    (hmem : st.memory = fun _ => 0) (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) :
    PaddedBytesAt (padState st).memory (Padding.paddedMessage input) := by
  intro k hk
  rw [Padding.paddedMessage_size] at hk
  by_cases hinput : k < input.size
  · rw [padState_input st input hmem hcd hfit k hinput,
      paddedMessage_input input k hinput]
  by_cases hsentinel : k = input.size
  · subst k
    rw [padState_sentinel st input hcd hfit, paddedMessage_sentinel]
  by_cases hfooter : Padding.paddedLength input.size - 8 ≤ k
  · let j := k - (Padding.paddedLength input.size - 8)
    have hj : j < 8 := by dsimp only [j]; omega
    have hkEq : k = Padding.paddedLength input.size - 8 + j := by
      dsimp only [j]
      omega
    rw [hkEq, padState_footer st input hcd hfit j hj,
      paddedMessage_footer input j hj]
  · have hlo : input.size < k := by omega
    have hhi : k < Padding.paddedLength input.size - 8 := by omega
    rw [padState_zero st input hmem hcd hfit k hlo hhi,
      paddedMessage_zero input k hlo hhi]

end Challenge.Ripemd160.Reference.Proofs.Yul.Execution
