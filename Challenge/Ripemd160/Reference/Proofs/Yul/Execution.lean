import Challenge.Ripemd160.Reference.Proofs.Yul.Driver
import Challenge.EvmProof.Bytes
import Challenge.YulProof.Interpreter

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
open StateModel
open Challenge.YulProof.EvmState
open Challenge.YulProof.Interpreter
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
  apply evalExpr_of_interp localExec_lawful (fuel := 20)
  interval_cases i <;> rfl

private theorem exec_padBody (funs : FunEnv localDialect) (original current : EvmState)
    (i : Nat) (hi : i ≤ 8) :
    ExecStmt localDialect funs (("i", BitVec.ofNat 256 i) :: padLoopTail original)
      current (.block padBody) (("i", BitVec.ofNat 256 i) :: padLoopTail original)
      (lengthStepState original current i) .normal := by
  apply execStmt_of_interp localExec_lawful (fuel := 100)
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
    have hraw := evalBuiltin localExec_lawful (op := .add) hargs hfn
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
    apply execStmt_of_interp localExec_lawful (fuel := 30)
    rfl
  have hPaddedLen : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", 0)] st
      padDecl.body[1]! [("n", n), ("paddedLen", paddedLen)] st .normal := by
    apply execStmt_of_interp localExec_lawful (fuel := 50)
    rfl
  have hCopy : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", paddedLen)] st
      padDecl.body[2]! [("n", n), ("paddedLen", paddedLen)] (calldataCopyState st) .normal := by
    apply execStmt_of_interp localExec_lawful (fuel := 80)
    rfl
  have hSentinel : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", paddedLen)]
      (calldataCopyState st) padDecl.body[3]! [("n", n), ("paddedLen", paddedLen)]
      (sentinelState st) .normal := by
    apply execStmt_of_interp localExec_lawful (fuel := 60)
    rfl
  have hBitLen : ExecStmt localDialect bodyFuns [("n", n), ("paddedLen", paddedLen)]
      (sentinelState st) padDecl.body[4]!
      [("bitLen", bitLen), ("n", n), ("paddedLen", paddedLen)]
      (sentinelState st) .normal := by
    apply execStmt_of_interp localExec_lawful (fuel := 40)
    rfl
  have hLenOff : ExecStmt localDialect bodyFuns
      [("bitLen", bitLen), ("n", n), ("paddedLen", paddedLen)] (sentinelState st)
      padDecl.body[5]! Vtail (sentinelState st) .normal := by
    apply execStmt_of_interp localExec_lawful (fuel := 50)
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
    (hcd : st.env.calldata = input.toList)
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
    (hmem : ∀ p, 0x800 ≤ p → st.memory p = 0)
    (hcd : st.env.calldata = input.toList)
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
  rw [hmem (0x800 + k) (by omega)]

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
    (hmem : ∀ p, 0x800 ≤ p → st.memory p = 0)
    (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) :
    PaddedBytesAt (padState st).memory (Padding.paddedMessage input) := by
  intro k hk
  rw [Padding.paddedMessage_size] at hk
  by_cases hinput : k < input.size
  · rw [padState_input st input hcd hfit k hinput,
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

/-- Padding is framed above the entire table/hash scratch region. -/
theorem padState_below (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input)
    (p : Nat) (hp : p < 0x800) :
    (padState st).memory p = st.memory p := by
  rw [padState, lengthPrefix_outside st (sentinelState st) input hcd hfit 8
    (by omega) p (by
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
  rw [show input.data.size = input.size by rfl, calldataSize_toNat input hfit]
  rw [if_neg (by omega)]

theorem loadWord_padState (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input)
    (p : Nat) (hp : p + 32 ≤ 0x800) :
    loadWord (padState st).memory p = loadWord st.memory p := by
  unfold loadWord
  apply List.foldl_ext _ _ 0
  intro acc i hi
  have hi' : i < 32 := List.mem_range.mp hi
  rw [padState_below st input hcd hfit (p + i) (by omega)]

theorem FixedLookupCorrect.padState {st : EvmState} {input : ByteArray}
    (fixed : FixedLookupCorrect st.memory)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input) :
    FixedLookupCorrect (padState st).memory where
  leftIndex i hi := by
    unfold tableValue
    rw [loadWord_padState st input hcd hfit]
    · simpa [tableValue] using fixed.leftIndex i hi
    · interval_cases i <;> decide
  rightIndex i hi := by
    unfold tableValue
    rw [loadWord_padState st input hcd hfit]
    · simpa [tableValue] using fixed.rightIndex i hi
    · interval_cases i <;> decide
  leftRotation i hi := by
    unfold tableValue
    rw [loadWord_padState st input hcd hfit]
    · simpa [tableValue] using fixed.leftRotation i hi
    · interval_cases i <;> decide
  rightRotation i hi := by
    unfold tableValue
    rw [loadWord_padState st input hcd hfit]
    · simpa [tableValue] using fixed.rightRotation i hi
    · interval_cases i <;> decide
  leftConstant i hi := by
    rw [loadWord_padState st input hcd hfit]
    · exact fixed.leftConstant i hi
    · interval_cases i <;> decide
  rightConstant i hi := by
    rw [loadWord_padState st input hcd hfit]
    · exact fixed.rightConstant i hi
    · interval_cases i <;> decide

theorem initTablesState_above (st : EvmState) (q : Nat) (hq : 0x800 ≤ q) :
    (initTablesState st).memory q = st.memory q := by
  apply MemoryEqFrom.storeMany st tableStores 0x800 (fun p v hm => ?_) q hq
  simp only [tableStores, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;> cases h <;> decide

def preparedState (st : EvmState) : EvmState :=
  padState (initHState (initTablesState st))

theorem preparedState_env (st : EvmState) : (preparedState st).env = st.env := by
  rfl

theorem preparedState_correct (st : EvmState) (input : ByteArray)
    (hmem : st.memory = fun _ => 0) (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) :
    PrefixCorrect (preparedState st) (Padding.paddedMessage input) 0 := by
  have hcd' : (initHState (initTablesState st)).env.calldata = input.toList := by
    change st.env.calldata = input.toList
    exact hcd
  constructor
  · rw [preparedState, compressPrefix]
    have hworking : workingAt (padState (initHState (initTablesState st))).memory 0x020 =
        workingAt (initHState (initTablesState st)).memory 0x020 := by
      apply sourceWorking_ext
      all_goals unfold workingAt
      all_goals apply loadWord_padState _ input hcd' hfit
      all_goals decide
    rw [hworking]
    simpa [hashPrefix] using workingAt_initHState (initTablesState st)
  · unfold preparedState
    apply FixedLookupCorrect.padState
    · apply FixedLookupCorrect.transport (fixedLookup_initTables st)
      exact initHState_above 0x4a0 (initTablesState st) (by omega)
    · exact hcd'
    · exact hfit
  · simpa [preparedState, compressPrefix] using
      padState_padded (initHState (initTablesState st)) input
        (by
          intro p hp
          rw [(initHState_above 0x800 (initTablesState st) (by omega)) p hp]
          rw [initTablesState_above st p hp, hmem]
        ) hcd' hfit

/-! ## Source block loop -/

def blockCount (input : ByteArray) : Nat :=
  Padding.paddedLength input.size / 64

private def blockBody : Block Op := yul% {
  compress(add(0x800, off))
}

private def blockPost : Block Op := yul% { off := add(off, 64) }

private theorem eval_blockCond (funs : FunEnv localDialect)
    (Vtail : VEnv localDialect) (st : EvmState) (input : ByteArray)
    (hfit : CalldataFits input) (n : Nat) (hn : n ≤ blockCount input) :
    EvalExpr localDialect funs
      (("off", BitVec.ofNat 256 (n * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      st (yulE% lt(off, paddedLen))
      (.vals [if n < blockCount input then (1 : U256) else 0] st) := by
  apply Step.builtinOk (D := localDialect)
    (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
  simp [localDialect, YulSemantics.EVM.evmWithExternal,
    YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.stepOp,
    YulSemantics.EVM.bin, BitVec.ult, YulSemantics.EVM.b2w]
  have hpadded : Padding.paddedLength input.size < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    have := hfit
    unfold CalldataFits at this
    norm_num at this ⊢
    omega
  have hn64 : n * 64 < 2 ^ 256 := by
    have heq := Padding.paddedLength_eq_blocks input.size
    unfold blockCount at hn
    omega
  norm_num only [Nat.reducePow] at hpadded hn64 ⊢
  rw [Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hpadded,
    Padding.paddedLength_eq_blocks]
  unfold blockCount
  by_cases h : n < Padding.paddedLength input.size / 64 <;> simp [h]

private theorem eval_blockArg (funs : FunEnv localDialect)
    (Vtail : VEnv localDialect) (st : EvmState) (input : ByteArray)
    (hfit : CalldataFits input) (n : Nat) (hn : n < blockCount input) :
    EvalExpr localDialect funs
      (("off", BitVec.ofNat 256 (n * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      st (yulE% add(0x800, off))
      (.vals [BitVec.ofNat 256 (0x800 + n * 64)] st) := by
  have hsum : 0x800 + n * 64 < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    have heq := Padding.paddedLength_eq_blocks input.size
    have := hfit
    unfold blockCount at hn
    unfold CalldataFits at this
    norm_num at this ⊢
    omega
  have heq : (0x800 : U256) + BitVec.ofNat 256 (n * 64) =
      BitVec.ofNat 256 (0x800 + n * 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (2048 + n * 64 % 2 ^ 256) % 2 ^ 256 =
      (2048 + n * 64) % 2 ^ 256
    norm_num only [Nat.reducePow] at hsum ⊢
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hsum]
    omega
  apply Step.builtinOk (D := localDialect)
    (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit)
  simpa [localDialect, YulSemantics.EVM.evmWithExternal,
    YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.stepOp,
    YulSemantics.EVM.bin, YulSemantics.EVM.litValue] using heq

private theorem exec_blockBody
    (Vtail : VEnv localDialect) (st : EvmState) (input : ByteArray)
    (hfit : CalldataFits input) (n : Nat) (hn : n < blockCount input) :
    ExecStmt localDialect ([] :: verifiedFunctions)
      (("off", BitVec.ofNat 256 (n * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      st (.block blockBody)
      (("off", BitVec.ofNat 256 (n * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      (compressionState st (BitVec.ofNat 256 (0x800 + n * 64))) .normal := by
  let funs : FunEnv localDialect := [] :: verifiedFunctions
  let innerFuns := hoist localDialect blockBody :: funs
  have harg := eval_blockArg innerFuns Vtail st input hfit n hn
  have hcall := eval_compress (BitVec.ofNat 256 (0x800 + n * 64)) (by rfl) harg
  have hseq := Step.seqCons (D := localDialect) (Step.exprStmt hcall)
    (Step.seqNil (D := localDialect))
  have hblock := Step.block (D := localDialect) hseq
  simpa [funs, innerFuns, blockBody, restore] using hblock

private theorem exec_blockPost (funs : FunEnv localDialect)
    (Vtail : VEnv localDialect) (st : EvmState) (input : ByteArray)
    (hfit : CalldataFits input) (n : Nat) (hn : n < blockCount input) :
    ExecStmt localDialect funs
      (("off", BitVec.ofNat 256 (n * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      st (.block blockPost)
      (("off", BitVec.ofNat 256 ((n + 1) * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      st .normal := by
  let innerFuns : FunEnv localDialect := hoist localDialect blockPost :: funs
  have hlt := Padding.paddedLength_lt input.size
  have heq := Padding.paddedLength_eq_blocks input.size
  have := hfit
  unfold blockCount at hn
  unfold CalldataFits at this
  have hsum : (n + 1) * 64 < 2 ^ 256 := by
    norm_num at this ⊢
    omega
  have haddEq : BitVec.ofNat 256 (n * 64) + (64 : U256) =
      BitVec.ofNat 256 ((n + 1) * 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (n * 64 % 2 ^ 256 + 64) % 2 ^ 256 =
      ((n + 1) * 64) % 2 ^ 256
    norm_num only [Nat.reducePow] at hsum ⊢
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hsum]
    omega
  have hadd : EvalExpr localDialect innerFuns
      (("off", BitVec.ofNat 256 (n * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      st (yulE% add(off, 64)) (.vals [BitVec.ofNat 256 ((n + 1) * 64)] st) := by
    have hargs : EvalArgs localDialect innerFuns
        (("off", BitVec.ofNat 256 (n * 64)) ::
          ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
        st [yulE% off, yulE% 64]
        (.vals [BitVec.ofNat 256 (n * 64), localDialect.litValue (.number 64)] st) :=
      Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)
    have hfn : localBuiltinFn .add
        [BitVec.ofNat 256 (n * 64), localDialect.litValue (.number 64)] st =
        some (.ok [BitVec.ofNat 256 (n * 64) + localDialect.litValue (.number 64)] st) := by
      rfl
    have hraw := evalBuiltin localExec_lawful (op := .add) hargs hfn
    rw [show localDialect.litValue (.number 64) = (64 : U256) by rfl,
      haddEq] at hraw
    simpa [mkCall, parse] using hraw
  have hassign := Step.assignVal (D := localDialect) (vars := ["off"]) hadd rfl
  have hset : VEnv.setMany
      (("off", BitVec.ofNat 256 (n * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail)
      ["off"] [BitVec.ofNat 256 ((n + 1) * 64)] =
      (("off", BitVec.ofNat 256 ((n + 1) * 64)) ::
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size)) :: Vtail) := by
    rfl
  rw [hset] at hassign
  have hseq := Step.seqCons (D := localDialect) hassign (Step.seqNil (D := localDialect))
  have hblock := Step.block (D := localDialect) hseq
  simpa [innerFuns, blockPost, restore] using hblock

theorem eval_blockLoop (initial : EvmState) (input : ByteArray)
    (hfit : CalldataFits input) :
    ExecLoop localDialect ([] :: verifiedFunctions)
      [("off", 0),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]
      initial (yulE% lt(off, paddedLen)) blockPost blockBody
      [("off", BitVec.ofNat 256 (blockCount input * 64)),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]
      (compressPrefix initial (blockCount input)) .normal := by
  let Vtail : VEnv localDialect := []
  let Inv : Nat → VEnv localDialect → EvmState → Prop :=
    fun remaining V current => ∃ n,
      n + remaining = blockCount input ∧
      V = [("off", BitVec.ofNat 256 (n * 64)),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))] ∧
      current = compressPrefix initial n
  have hdone : ∀ V current, Inv 0 V current →
      ∃ cv current', EvalExpr localDialect ([] :: verifiedFunctions) V current
        (yulE% lt(off, paddedLen)) (.vals [cv] current') ∧
        cv = 0 ∧ Inv 0 V current' := by
    intro V current hInv
    obtain ⟨n, hn, rfl, rfl⟩ := hInv
    have hnEq : n = blockCount input := by omega
    subst n
    have hcond := eval_blockCond ([] :: verifiedFunctions) []
      (compressPrefix initial (blockCount input)) input hfit (blockCount input) (by omega)
    exact ⟨0, _, by simpa using hcond, rfl, blockCount input, by omega, rfl, rfl⟩
  have hstep : ∀ remaining V current, Inv (remaining + 1) V current →
      ∃ cv currentCond Vb currentBody ob Vp currentPost,
        EvalExpr localDialect ([] :: verifiedFunctions) V current
          (yulE% lt(off, paddedLen)) (.vals [cv] currentCond) ∧ cv ≠ 0 ∧
        ExecStmt localDialect ([] :: verifiedFunctions) V currentCond (.block blockBody)
          Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
        ExecStmt localDialect ([] :: verifiedFunctions) Vb currentBody (.block blockPost)
          Vp currentPost .normal ∧ Inv remaining Vp currentPost := by
    intro remaining V current hInv
    obtain ⟨n, hn, rfl, rfl⟩ := hInv
    have hnlt : n < blockCount input := by omega
    refine ⟨(1 : U256), compressPrefix initial n,
      [("off", BitVec.ofNat 256 (n * 64)),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))],
      compressPrefix initial (n + 1), .normal,
      [("off", BitVec.ofNat 256 ((n + 1) * 64)),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))],
      compressPrefix initial (n + 1), ?_, by decide, ?_, Or.inl rfl, ?_, ?_⟩
    · simpa [hnlt] using eval_blockCond _ Vtail _ input hfit n (by omega)
    · simpa [compressPrefix] using exec_blockBody Vtail
        (compressPrefix initial n) input hfit n hnlt
    · exact exec_blockPost _ Vtail _ input hfit n hnlt
    · exact ⟨n + 1, by omega, rfl, rfl⟩
  obtain ⟨V', current', hloop, hInv⟩ :=
    ExecLoop.countdown (D := localDialect) (funs := [] :: verifiedFunctions)
      (cond := yulE% lt(off, paddedLen)) (post := blockPost) (body := blockBody)
      (Inv := Inv) hdone hstep (blockCount input)
      [("off", 0),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]
      initial ⟨0, by omega, rfl, rfl⟩
  obtain ⟨n, hn, hV, hstate⟩ := hInv
  have hnEq : n = blockCount input := by omega
  subst n
  subst V'
  subst current'
  simpa [blockBody, blockPost] using hloop

theorem finalPrefix_correct (st : EvmState) (input : ByteArray)
    (hmem : st.memory = fun _ => 0) (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) :
    PrefixCorrect (preparedState st) (Padding.paddedMessage input) (blockCount input) := by
  have hzero := preparedState_correct st input hmem hcd hfit
  apply compressPrefix_correct (preparedState st) (Padding.paddedMessage input)
    (blockCount input)
  · rw [Padding.paddedMessage_size]
    unfold blockCount
    omega
  · rw [Padding.paddedMessage_size]
    have hlt := Padding.paddedLength_lt input.size
    have := hfit
    unfold CalldataFits at this
    norm_num at this ⊢
    omega
  · exact hzero.hash
  · exact hzero.fixed
  · exact hzero.padded

theorem finalHash_eq (input : ByteArray) :
    CompressionCorrect.hashArray
        (hashPrefix (Padding.paddedMessage input) (blockCount input)) =
      SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
        (Padding.paddedMessage input) 0 (blockCount input) := by
  exact hashArray_hashPrefix _ _

/-! ## Digest serialization -/

def writeStepState (st : EvmState) (off w : U256) (i : Nat) : EvmState :=
  let p := off + BitVec.ofNat 256 i
  let value := (w >>> (8 * i)) &&& 0xff
  { touchMemory st p.toNat 1 with memory := storeByte st.memory p.toNat value }

def writePrefix (off w : U256) : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st => writeStepState (writePrefix off w i st) off w i

private def writeBody : Block Op := yul% {
  mstore8(add(off, i), and(shr(mul(8, i), w), 0xff))
}

private def writeLE32Decl : FDecl localDialect where
  params := ["off", "w"]
  rets := []
  body := yul% {
    for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
      mstore8(add(off, i), and(shr(mul(8, i), w), 0xff))
    }
  }

private theorem exec_writeLE32Body (st : EvmState) (off w : U256) :
    ExecStmt localDialect verifiedFunctions [("off", off), ("w", w)] st
      (.block writeLE32Decl.body) [("off", off), ("w", w)]
      (writePrefix off w 4 st) .normal := by
  let Vtail : VEnv localDialect := [("off", off), ("w", w)]
  let bodyFuns : FunEnv localDialect := [] :: verifiedFunctions
  let loopFuns : FunEnv localDialect := [] :: bodyFuns
  have hcond (i : Nat) (hi : i ≤ 4) (current : EvmState) :
      EvalExpr localDialect loopFuns (("i", BitVec.ofNat 256 i) :: Vtail) current
        (yulE% lt(i, 4)) (.vals [if i < 4 then (1 : U256) else 0] current) := by
    apply evalExpr_of_interp localExec_lawful (fuel := 20)
    interval_cases i <;> rfl
  have hbody (i : Nat) (hi : i ≤ 4) (current : EvmState) :
      ExecStmt localDialect loopFuns (("i", BitVec.ofNat 256 i) :: Vtail) current
        (.block writeBody) (("i", BitVec.ofNat 256 i) :: Vtail)
        (writeStepState current off w i) .normal := by
    apply execStmt_of_interp localExec_lawful (fuel := 100)
    interval_cases i <;> rfl
  simp only [writeLE32Decl]
  refine Step.block (D := localDialect) (Vb := Vtail) ?_
  refine Step.seqCons (D := localDialect) ?_ Step.seqNil
  refine Step.forLoop (D := localDialect)
    (Vinit := ("i", 0) :: Vtail) (stinit := st)
    (Vend := ("i", BitVec.ofNat 256 4) :: Vtail) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · let Inv : Nat → VEnv localDialect → EvmState → Prop :=
      fun remaining V current => ∃ i,
        i + remaining = 4 ∧ V = ("i", BitVec.ofNat 256 i) :: Vtail ∧
          current = writePrefix off w i st
    have hdone : ∀ V current, Inv 0 V current →
        ∃ cv current', EvalExpr localDialect loopFuns V current (yulE% lt(i, 4))
          (.vals [cv] current') ∧ cv = 0 ∧ Inv 0 V current' := by
      intro V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hiEq : i = 4 := by omega
      subst i
      exact ⟨0, _, hcond 4 (by omega) _, rfl, 4, by omega, rfl, rfl⟩
    have hstep : ∀ remaining V current, Inv (remaining + 1) V current →
        ∃ cv currentCond Vb currentBody ob Vp currentPost,
          EvalExpr localDialect loopFuns V current (yulE% lt(i, 4))
            (.vals [cv] currentCond) ∧ cv ≠ 0 ∧
          ExecStmt localDialect loopFuns V currentCond (.block writeBody)
            Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
          ExecStmt localDialect loopFuns Vb currentBody (.block padPost)
            Vp currentPost .normal ∧ Inv remaining Vp currentPost := by
      intro remaining V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hi4 : i < 4 := by omega
      refine ⟨(1 : U256), writePrefix off w i st,
        ("i", BitVec.ofNat 256 i) :: Vtail, writePrefix off w (i + 1) st, .normal,
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail, writePrefix off w (i + 1) st,
        ?_, by decide, ?_, Or.inl rfl, ?_, ?_⟩
      · simpa [hi4] using hcond i (by omega) (writePrefix off w i st)
      · simpa [writePrefix] using hbody i (by omega) (writePrefix off w i st)
      · exact exec_padPost loopFuns _ Vtail i (by omega)
      · exact ⟨i + 1, by omega, rfl, rfl⟩
    obtain ⟨V', current', hloop, hInv⟩ :=
      ExecLoop.countdown (D := localDialect) (funs := loopFuns)
        (cond := yulE% lt(i, 4)) (post := padPost) (body := writeBody)
        (Inv := Inv) hdone hstep 4 (("i", 0) :: Vtail) st
        ⟨0, by omega, rfl, rfl⟩
    obtain ⟨i, hi, hV, hstate⟩ := hInv
    have hiEq : i = 4 := by omega
    subst i
    subst V'
    subst current'
    simpa [loopFuns, bodyFuns, writeBody, padPost, Vtail, writeLE32Decl,
      hoist] using hloop

theorem eval_writeLE32 {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {args : List (Expr Op)} (off w : U256)
    (hlookup : lookupFun funs "writeLE32" = some (writeLE32Decl, verifiedFunctions))
    (hargs : EvalArgs localDialect funs V st args (.vals [off, w] st1)) :
    EvalExpr localDialect funs V st (.call "writeLE32" args)
      (.vals [] (writePrefix off w 4 st1)) := by
  exact Step.callOk (D := localDialect) hargs hlookup rfl
    (exec_writeLE32Body st1 off w) (Or.inl rfl)

def hAtValue (st : EvmState) (i : Nat) : U256 :=
  loadWord st.memory (0x20 + BitVec.ofNat 256 i * 32).toNat

def hAtState (st : EvmState) (i : Nat) : EvmState :=
  touchMemory st (0x20 + BitVec.ofNat 256 i * 32).toNat 32

private def hAtDecl : FDecl localDialect where
  params := ["i"]
  rets := ["v"]
  body := yul% { v := mload(add(0x20, mul(i, 32))) }

private theorem exec_hAtBody (st : EvmState) (i : Nat) :
    ExecStmt localDialect verifiedFunctions
      [("i", BitVec.ofNat 256 i), ("v", 0)] st (.block hAtDecl.body)
      [("i", BitVec.ofNat 256 i), ("v", hAtValue st i)] (hAtState st i) .normal := by
  apply execStmt_of_interp localExec_lawful (fuel := 80)
  rfl

private theorem eval_hAt {funs : FunEnv localDialect} {V : VEnv localDialect}
    {st st1 : EvmState} {arg : Expr Op} (i : Nat)
    (hlookup : lookupFun funs "hAt" = some (hAtDecl, verifiedFunctions))
    (harg : EvalExpr localDialect funs V st arg
      (.vals [BitVec.ofNat 256 i] st1)) :
    EvalExpr localDialect funs V st (.call "hAt" [arg])
      (.vals [hAtValue st1 i] (hAtState st1 i)) := by
  exact Step.callOk (D := localDialect) (Step.argsCons Step.argsNil harg)
    hlookup rfl (exec_hAtBody st1 i) (Or.inl rfl)

def zeroOutputState (st : EvmState) : EvmState := storeWordAt st 0 0

def outputStepState (st : EvmState) (i : Nat) : EvmState :=
  writePrefix (BitVec.ofNat 256 (12 + i * 4)) (hAtValue st i) 4 (hAtState st i)

def outputPrefix : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st => outputStepState (outputPrefix i st) i

private theorem writePrefix_memory_above (st : EvmState) (off w : U256)
    (n q : Nat) (hbound : off.toNat + n ≤ 32) (hq : 32 ≤ q) :
    (writePrefix off w n st).memory q = st.memory q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [writePrefix]
      change storeByte (writePrefix off w n st).memory
        (off + BitVec.ofNat 256 n).toNat _ q = st.memory q
      have hp : (off + BitVec.ofNat 256 n).toNat = off.toNat + n := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [storeByte, if_neg (by omega), ih (by omega)]

private theorem outputPrefix_memory_above (st : EvmState) (n q : Nat)
    (hn : n ≤ 5) (hq : 32 ≤ q) :
    (outputPrefix n st).memory q = st.memory q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [outputPrefix]
      unfold outputStepState
      rw [writePrefix_memory_above _ _ _ 4 q]
      · change (outputPrefix n st).memory q = st.memory q
        exact ih (by omega)
      · norm_num [BitVec.toNat_ofNat]
        omega
      · exact hq

private theorem zeroOutputState_memory_above (st : EvmState) (q : Nat)
    (hq : 32 ≤ q) : (zeroOutputState st).memory q = st.memory q := by
  unfold zeroOutputState storeWordAt
  change storeWord st.memory 0 0 q = st.memory q
  rw [storeWord, if_neg (by omega)]

private theorem loadWord_congr_above (left right : Nat → UInt8) (p : Nat)
    (h : ∀ q, p ≤ q → left q = right q) :
    loadWord left p = loadWord right p := by
  unfold loadWord
  congr 1
  funext acc j
  rw [h (p + j) (by omega)]

private theorem hAtValue_outputPrefix (st : EvmState) (n i : Nat)
    (hn : n ≤ 5) (hi : i < 5) :
    hAtValue (outputPrefix n st) i = hAtValue st i := by
  unfold hAtValue
  apply loadWord_congr_above
  intro q hq
  apply outputPrefix_memory_above st n q hn
  have hp : (32 + BitVec.ofNat 256 i * 32 : U256).toNat = 32 + i * 32 := by
    interval_cases i <;> decide
  rw [hp] at hq
  omega

private theorem hAtValue_zeroOutputState (st : EvmState) (i : Nat) (hi : i < 5) :
    hAtValue (zeroOutputState st) i = hAtValue st i := by
  unfold hAtValue
  apply loadWord_congr_above
  intro q hq
  apply zeroOutputState_memory_above
  have hp : (32 + BitVec.ofNat 256 i * 32 : U256).toNat = 32 + i * 32 := by
    interval_cases i <;> decide
  rw [hp] at hq
  omega

private def outputBody : Block Op := yul% {
  writeLE32(add(12, mul(i, 4)), hAt(i))
}

private theorem eval_outputCond (funs : FunEnv localDialect)
    (Vtail : VEnv localDialect) (st : EvmState) (i : Nat) (hi : i ≤ 5) :
    EvalExpr localDialect funs (("i", BitVec.ofNat 256 i) :: Vtail) st
      (yulE% lt(i, 5)) (.vals [if i < 5 then (1 : U256) else 0] st) := by
  apply evalExpr_of_interp localExec_lawful (fuel := 20)
  interval_cases i <;> rfl

private theorem eval_outputOffset (funs : FunEnv localDialect)
    (Vtail : VEnv localDialect) (st : EvmState) (i : Nat) (hi : i ≤ 5) :
    EvalExpr localDialect funs (("i", BitVec.ofNat 256 i) :: Vtail) st
      (yulE% add(12, mul(i, 4)))
      (.vals [BitVec.ofNat 256 (12 + i * 4)] st) := by
  apply evalExpr_of_interp localExec_lawful (fuel := 30)
  interval_cases i <;> rfl

private theorem exec_outputBody (Vtail : VEnv localDialect)
    (st : EvmState) (i : Nat) (hi : i < 5) :
    ExecStmt localDialect ([] :: verifiedFunctions)
      (("i", BitVec.ofNat 256 i) :: Vtail) st (.block outputBody)
      (("i", BitVec.ofNat 256 i) :: Vtail) (outputStepState st i) .normal := by
  let funs : FunEnv localDialect := [] :: verifiedFunctions
  let innerFuns : FunEnv localDialect := hoist localDialect outputBody :: funs
  have hhAt : EvalExpr localDialect innerFuns
      (("i", BitVec.ofNat 256 i) :: Vtail) st (yulE% hAt(i))
      (.vals [hAtValue st i] (hAtState st i)) := by
    apply eval_hAt i (by rfl)
    exact Step.var rfl
  have hoff := eval_outputOffset innerFuns Vtail (hAtState st i) i (by omega)
  have hargs : EvalArgs localDialect innerFuns
      (("i", BitVec.ofNat 256 i) :: Vtail) st
      [yulE% add(12, mul(i, 4)), yulE% hAt(i)]
      (.vals [BitVec.ofNat 256 (12 + i * 4), hAtValue st i] (hAtState st i)) :=
    Step.argsCons (Step.argsCons Step.argsNil hhAt) hoff
  have hwrite := eval_writeLE32 (BitVec.ofNat 256 (12 + i * 4))
    (hAtValue st i) (by rfl) hargs
  have hseq := Step.seqCons (D := localDialect) (Step.exprStmt hwrite)
    (Step.seqNil (D := localDialect))
  have hblock := Step.block (D := localDialect) hseq
  simpa [funs, innerFuns, outputBody, outputStepState, restore] using hblock

theorem eval_outputLoop (st : EvmState) (Vtail : VEnv localDialect) :
    ExecLoop localDialect ([] :: verifiedFunctions) (("i", 0) :: Vtail) st
      (yulE% lt(i, 5)) padPost outputBody
      (("i", BitVec.ofNat 256 5) :: Vtail) (outputPrefix 5 st) .normal := by
  let Inv : Nat → VEnv localDialect → EvmState → Prop :=
    fun remaining V current => ∃ i,
      i + remaining = 5 ∧ V = ("i", BitVec.ofNat 256 i) :: Vtail ∧
        current = outputPrefix i st
  have hdone : ∀ V current, Inv 0 V current →
      ∃ cv current', EvalExpr localDialect ([] :: verifiedFunctions) V current
        (yulE% lt(i, 5)) (.vals [cv] current') ∧ cv = 0 ∧ Inv 0 V current' := by
    intro V current hInv
    obtain ⟨i, hi, rfl, rfl⟩ := hInv
    have hiEq : i = 5 := by omega
    subst i
    exact ⟨0, _, eval_outputCond _ Vtail _ 5 (by omega), rfl,
      5, by omega, rfl, rfl⟩
  have hstep : ∀ remaining V current, Inv (remaining + 1) V current →
      ∃ cv currentCond Vb currentBody ob Vp currentPost,
        EvalExpr localDialect ([] :: verifiedFunctions) V current
          (yulE% lt(i, 5)) (.vals [cv] currentCond) ∧ cv ≠ 0 ∧
        ExecStmt localDialect ([] :: verifiedFunctions) V currentCond (.block outputBody)
          Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
        ExecStmt localDialect ([] :: verifiedFunctions) Vb currentBody (.block padPost)
          Vp currentPost .normal ∧ Inv remaining Vp currentPost := by
    intro remaining V current hInv
    obtain ⟨i, hi, rfl, rfl⟩ := hInv
    have hi5 : i < 5 := by omega
    refine ⟨(1 : U256), outputPrefix i st, ("i", BitVec.ofNat 256 i) :: Vtail,
      outputPrefix (i + 1) st, .normal, ("i", BitVec.ofNat 256 (i + 1)) :: Vtail,
      outputPrefix (i + 1) st, ?_, by decide, ?_, Or.inl rfl, ?_, ?_⟩
    · simpa [hi5] using eval_outputCond _ Vtail (outputPrefix i st) i (by omega)
    · simpa [outputPrefix] using exec_outputBody Vtail (outputPrefix i st) i hi5
    · exact exec_padPost _ _ Vtail i (by omega)
    · exact ⟨i + 1, by omega, rfl, rfl⟩
  obtain ⟨V', current', hloop, hInv⟩ :=
    ExecLoop.countdown (D := localDialect) (funs := [] :: verifiedFunctions)
      (cond := yulE% lt(i, 5)) (post := padPost) (body := outputBody)
      (Inv := Inv) hdone hstep 5 (("i", 0) :: Vtail) st
      ⟨0, by omega, rfl, rfl⟩
  obtain ⟨i, hi, hV, hstate⟩ := hInv
  have hiEq : i = 5 := by omega
  subst i
  subst V'
  subst current'
  exact hloop

def compressedState (st : EvmState) (input : ByteArray) : EvmState :=
  compressPrefix (preparedState st) (blockCount input)

def serializedState (st : EvmState) (input : ByteArray) : EvmState :=
  outputPrefix 5 (zeroOutputState (compressedState st input))

def writtenByte (w : U256) (j : Nat) : UInt8 :=
  byteAt ((w >>> (8 * j)) &&& 0xff) 0

def sourceWordBytes (w : U256) : List UInt8 :=
  [writtenByte w 0, writtenByte w 1, writtenByte w 2, writtenByte w 3]

private theorem writtenByte_ofUInt32 (w : UInt32) (j : Nat) (hj : j < 4) :
    writtenByte (BitVec.ofNat 256 w.toNat) j =
      ((w >>> UInt32.ofNat (8 * j)) &&& 0xff).toUInt8 := by
  apply UInt8.toNat_inj.mp
  unfold writtenByte byteAt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat,
    UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_and,
    UInt32.toNat_shiftRight, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.lt_trans w.toNat_lt (by norm_num))]
  have hshift : 8 * j < 32 := by omega
  norm_num only [Nat.reducePow, Nat.reduceMod, Nat.shiftRight_zero]
  have hshiftBig : 8 * j < 4294967296 := by omega
  have hffBV : BitVec.toNat (255 : U256) = 255 := by decide
  have hff32 : UInt32.toNat (255 : UInt32) = 255 := by decide
  rw [hffBV, hff32, Nat.mod_eq_of_lt hshiftBig, Nat.mod_eq_of_lt hshift]

private theorem sourceWordBytes_ofUInt32 (w : UInt32) :
    sourceWordBytes (BitVec.ofNat 256 w.toNat) =
      (EvmSemantics.Crypto.Ripemd160.writeLE32 ByteArray.empty w).toList := by
  rw [show sourceWordBytes (BitVec.ofNat 256 w.toNat) = [
      ((w >>> UInt32.ofNat 0) &&& 0xff).toUInt8,
      ((w >>> UInt32.ofNat 8) &&& 0xff).toUInt8,
      ((w >>> UInt32.ofNat 16) &&& 0xff).toUInt8,
      ((w >>> UInt32.ofNat 24) &&& 0xff).toUInt8] by
    simp only [sourceWordBytes, writtenByte_ofUInt32 w 0 (by omega),
      writtenByte_ofUInt32 w 1 (by omega), writtenByte_ofUInt32 w 2 (by omega),
      writtenByte_ofUInt32 w 3 (by omega)]]
  unfold EvmSemantics.Crypto.Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [ByteArray.toList_eq_data]
  simp [Array.toList_push]
  rfl

private theorem writeLE32_append (acc : ByteArray) (w : UInt32) :
    EvmSemantics.Crypto.Ripemd160.writeLE32 acc w =
      acc ++ EvmSemantics.Crypto.Ripemd160.writeLE32 ByteArray.empty w := by
  unfold EvmSemantics.Crypto.Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  cases acc with
  | mk bytes =>
      congr 1
      apply Array.ext'
      simp [Array.toList_push, List.append_assoc]
      rfl

private theorem sourceWords_eq_emitDigest (h : Compression.HashState) :
    sourceWordBytes (BitVec.ofNat 256 h.h0.toNat) ++
        sourceWordBytes (BitVec.ofNat 256 h.h1.toNat) ++
        sourceWordBytes (BitVec.ofNat 256 h.h2.toNat) ++
        sourceWordBytes (BitVec.ofNat 256 h.h3.toNat) ++
        sourceWordBytes (BitVec.ofNat 256 h.h4.toNat) =
      (SpecBridge.emitDigest (CompressionCorrect.hashArray h)).toList := by
  unfold SpecBridge.emitDigest CompressionCorrect.hashArray
  norm_num [List.range, List.range.loop]
  conv_rhs =>
    rw [writeLE32_append]
    rw [writeLE32_append]
    rw [writeLE32_append]
    rw [writeLE32_append]
  rw [ByteArray.toList_eq_data]
  simp only [ByteArray.data_append, Array.toList_append]
  rw [sourceWordBytes_ofUInt32, sourceWordBytes_ofUInt32,
    sourceWordBytes_ofUInt32, sourceWordBytes_ofUInt32,
    sourceWordBytes_ofUInt32]
  simp [ByteArray.toList_eq_data]

def sourceOutput (st : EvmState) : List UInt8 :=
  List.replicate 12 0 ++ sourceWordBytes (hAtValue st 0) ++
    sourceWordBytes (hAtValue st 1) ++ sourceWordBytes (hAtValue st 2) ++
    sourceWordBytes (hAtValue st 3) ++ sourceWordBytes (hAtValue st 4)

@[simp] theorem sourceOutput_length (st : EvmState) : (sourceOutput st).length = 32 := by
  simp [sourceOutput, sourceWordBytes]

private theorem sourceOutput_eq_map (st : EvmState) :
    sourceOutput st = (List.range 32).map (fun p =>
      if p < 12 then 0 else
        writtenByte (hAtValue st ((p - 12) / 4)) ((p - 12) % 4)) := by
  norm_num [sourceOutput, sourceWordBytes, List.replicate, List.range, List.range.loop]

private theorem serializedState_memory_lt32 (st : EvmState) (input : ByteArray)
    (p : Nat) (hp : p < 32) :
    (serializedState st input).memory p =
      if p < 12 then 0 else
        writtenByte (hAtValue (compressedState st input) ((p - 12) / 4))
          ((p - 12) % 4) := by
  let base := zeroOutputState (compressedState st input)
  have h0 : hAtValue base 0 = hAtValue (compressedState st input) 0 := by
    exact hAtValue_zeroOutputState _ 0 (by omega)
  have h1 : hAtValue (outputPrefix 1 base) 1 = hAtValue (compressedState st input) 1 := by
    rw [hAtValue_outputPrefix base 1 1 (by omega) (by omega),
      hAtValue_zeroOutputState _ 1 (by omega)]
  have h2 : hAtValue (outputPrefix 2 base) 2 = hAtValue (compressedState st input) 2 := by
    rw [hAtValue_outputPrefix base 2 2 (by omega) (by omega),
      hAtValue_zeroOutputState _ 2 (by omega)]
  have h3 : hAtValue (outputPrefix 3 base) 3 = hAtValue (compressedState st input) 3 := by
    rw [hAtValue_outputPrefix base 3 3 (by omega) (by omega),
      hAtValue_zeroOutputState _ 3 (by omega)]
  have h4 : hAtValue (outputPrefix 4 base) 4 = hAtValue (compressedState st input) 4 := by
    rw [hAtValue_outputPrefix base 4 4 (by omega) (by omega),
      hAtValue_zeroOutputState _ 4 (by omega)]
  simp only [outputPrefix, outputStepState] at h1 h2 h3
  simp only [serializedState, outputPrefix, outputStepState]
  change (writePrefix 28 (hAtValue (outputPrefix 4 base) 4) 4
    (hAtState (outputPrefix 4 base) 4)).memory p = _
  rw [h4]
  simp only [outputPrefix, outputStepState]
  rw [h3, h2, h1, h0]
  interval_cases p <;>
    simp [base, writePrefix, writeStepState, hAtState, zeroOutputState,
      storeWordAt, touchMemory, storeByte, storeWord, writtenByte, byteAt]

theorem readBytes_serializedState (st : EvmState) (input : ByteArray) :
    readBytes (serializedState st input).memory 0 32 =
      sourceOutput (compressedState st input) := by
  unfold readBytes
  rw [sourceOutput_eq_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simpa using serializedState_memory_lt32 st input i hi

private theorem spec_eq_hash (input : ByteArray) :
    spec input = ByteArray.mk (Array.replicate 12 0) ++
      EvmSemantics.Crypto.Ripemd160.hash input := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

private theorem spec_toList_eq_hash (input : ByteArray) :
    (spec input).toList = List.replicate 12 0 ++
      (EvmSemantics.Crypto.Ripemd160.hash input).toList := by
  rw [spec_eq_hash]
  rw [ByteArray.toList_eq_data, ByteArray.data_append, Array.toList_append]
  simp [ByteArray.toList_eq_data]

theorem sourceOutput_compressed_eq_spec (st : EvmState) (input : ByteArray)
    (hmem : st.memory = fun _ => 0) (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) :
    sourceOutput (compressedState st input) = (spec input).toList := by
  have hp := finalPrefix_correct st input hmem hcd hfit
  have ha := congrArg SourceWorking.a hp.hash
  have hb := congrArg SourceWorking.b hp.hash
  have hc := congrArg SourceWorking.c hp.hash
  have hd := congrArg SourceWorking.d hp.hash
  have he := congrArg SourceWorking.e hp.hash
  have ha' : hAtValue (compressedState st input) 0 =
      BitVec.ofNat 256 (hashPrefix (Padding.paddedMessage input)
        (blockCount input)).h0.toNat := by
    simpa [compressedState, hAtValue, workingAt, sourceWorkingOf,
      CompressionCorrect.workingOfHash] using ha
  have hb' : hAtValue (compressedState st input) 1 =
      BitVec.ofNat 256 (hashPrefix (Padding.paddedMessage input)
        (blockCount input)).h1.toNat := by
    simpa [compressedState, hAtValue, workingAt, sourceWorkingOf,
      CompressionCorrect.workingOfHash] using hb
  have hc' : hAtValue (compressedState st input) 2 =
      BitVec.ofNat 256 (hashPrefix (Padding.paddedMessage input)
        (blockCount input)).h2.toNat := by
    simpa [compressedState, hAtValue, workingAt, sourceWorkingOf,
      CompressionCorrect.workingOfHash] using hc
  have hd' : hAtValue (compressedState st input) 3 =
      BitVec.ofNat 256 (hashPrefix (Padding.paddedMessage input)
        (blockCount input)).h3.toNat := by
    simpa [compressedState, hAtValue, workingAt, sourceWorkingOf,
      CompressionCorrect.workingOfHash] using hd
  have he' : hAtValue (compressedState st input) 4 =
      BitVec.ofNat 256 (hashPrefix (Padding.paddedMessage input)
        (blockCount input)).h4.toNat := by
    simpa [compressedState, hAtValue, workingAt, sourceWorkingOf,
      CompressionCorrect.workingOfHash] using he
  rw [sourceOutput, ha', hb', hc', hd', he']
  simp only [List.append_assoc]
  have hwords := sourceWords_eq_emitDigest
    (hashPrefix (Padding.paddedMessage input) (blockCount input))
  simp only [List.append_assoc] at hwords
  rw [hwords]
  rw [finalHash_eq input]
  rw [spec_toList_eq_hash]
  congr 1
  exact congrArg ByteArray.toList
    (HashSpecBridge.paddedHash_eq_hash input)

theorem serializedState_returns_digest (st : EvmState) (input : ByteArray)
    (hmem : st.memory = fun _ => 0) (hcd : st.env.calldata = input.toList)
    (hfit : CalldataFits input) :
    readBytes (serializedState st input).memory 0 32 = digestOf input.toList := by
  rw [readBytes_serializedState,
    sourceOutput_compressed_eq_spec st input hmem hcd hfit]
  simp [digestOf, mkCode_toList]

def returnState (st : EvmState) : EvmState :=
  { touchMemory st 0 32 with halted := some (.ret, readBytes st.memory 0 32) }

private theorem eval_zeroOutput (funs : FunEnv localDialect)
    (V : VEnv localDialect) (st : EvmState) :
    EvalExpr localDialect funs V st (yulE% mstore(0, 0))
      (.vals [] (zeroOutputState st)) := by
  apply evalExpr_of_interp localExec_lawful (fuel := 30)
  rfl

private theorem eval_return32 (funs : FunEnv localDialect)
    (V : VEnv localDialect) (st : EvmState) :
    EvalExpr localDialect funs V st
      (mkCall "return" [.lit (.number 0), .lit (.number 32)])
      (.halt (returnState st)) := by
  apply evalExpr_of_interp localExec_lawful (fuel := 30)
  rfl

/-- Exact execution of the complete auditable Yul AST, with no target EVM
execution judgment. -/
theorem run_verifiedProgram (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hfit : CalldataFits input) :
    Run localDialect verifiedProgram st []
      (returnState (serializedState st input)) .halt := by
  have hcdH : (initHState (initTablesState st)).env.calldata = input.toList := by
    change st.env.calldata = input.toList
    exact hcd
  have hpad := eval_pad (initHState (initTablesState st))
  have hpadded := paddedLengthValue_eq (initHState (initTablesState st)) input hcdH hfit
  rw [hpadded] at hpad
  have hpad' : EvalExpr localDialect verifiedFunctions []
      (initHState (initTablesState st)) (mkCall "pad" [])
      (.vals [BitVec.ofNat 256 (Padding.paddedLength input.size)]
        (padState (initHState (initTablesState st)))) := by
    have hpadName : parse "pad" = none := by decide
    simpa [mkCall, hpadName] using hpad
  have hblocks := eval_blockLoop (preparedState st) input hfit
  let compressed := compressedState st input
  let zeroed := zeroOutputState compressed
  have houtput := eval_outputLoop zeroed
    [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]
  show ExecStmt localDialect [] [] st (.block verifiedProgram) []
    (returnState (serializedState st input)) .halt
  simp only [verifiedProgram]
  refine Step.block (D := localDialect)
    (Vb := [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]) ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons (Step.exprStmt (eval_initTables st)) ?_
  refine Step.seqCons (Step.exprStmt (eval_initHCall (initTablesState st))) ?_
  refine Step.seqCons
    (V1 := [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))])
    (st1 := preparedState st) ?_ ?_
  · simpa [verifiedFunctions, verifiedProgram, preparedState] using
      (Step.letVal (D := localDialect) (vars := ["paddedLen"]) hpad' rfl)
  refine Step.seqCons
    (V1 := [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))])
    (st1 := compressedState st input) ?_ ?_
  · refine Step.forLoop (D := localDialect)
      (Vinit := [("off", 0),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))])
      (stinit := preparedState st)
      (Vend := [("off", BitVec.ofNat 256 (blockCount input * 64)),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa [verifiedFunctions, verifiedProgram, blockBody, blockPost,
        compressedState, hoist] using hblocks
  refine Step.seqCons (Step.exprStmt (eval_zeroOutput verifiedFunctions _
    (compressedState st input))) ?_
  refine Step.seqCons
    (V1 := [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))])
    (st1 := serializedState st input) ?_ ?_
  · refine Step.forLoop (D := localDialect)
      (Vinit := [("i", 0),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))])
      (stinit := zeroed)
      (Vend := [("i", BitVec.ofNat 256 5),
        ("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa [verifiedFunctions, verifiedProgram, outputBody, padPost, zeroed,
        serializedState, hoist] using houtput
  change ExecStmts localDialect verifiedFunctions
    [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]
    (serializedState st input)
    [.exprStmt (mkCall "return" [.lit (.number 0), .lit (.number 32)])]
    [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]
    (returnState (serializedState st input)) .halt
  exact Step.seqStop (Step.exprStmtHalt
    (eval_return32 verifiedFunctions
      [("paddedLen", BitVec.ofNat 256 (Padding.paddedLength input.size))]
      (serializedState st input))) (by decide)

/-- The direct source proof: the complete Yul block returns the specified
RIPEMD-160 precompile result for every admitted calldata value. -/
theorem verifiedProgram_computesDigest : ComputesDigest verifiedProgram := by
  intro st hpre
  obtain ⟨hmem, _hnotHalted, input, hcd, hfit⟩ := hpre
  refine ⟨[], returnState (serializedState st input), .halt,
    run_verifiedProgram st input hcd hfit, rfl, ?_⟩
  change some (HaltKind.ret,
    readBytes (serializedState st input).memory 0 32) = _
  rw [serializedState_returns_digest st input hmem hcd hfit, hcd]

end Challenge.Ripemd160.Reference.Proofs.Yul.Execution
