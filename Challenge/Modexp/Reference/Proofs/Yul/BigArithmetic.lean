import Challenge.Modexp.Reference.Proofs.Yul.Procedures
import Challenge.Modexp.Reference.Proofs.Limbs
import Challenge.YulProof.Interpreter

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Direct source-Yul contracts for MODEXP big arithmetic

`addMaskedMod` is split into the same addition, subtraction-candidate, and
selection phases as the source.  The definitions below are exact `EvmState`
transformers; their memory operations use the shared Yul-proof root library.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigArithmetic

open YulSemantics
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open Challenge.YulProof.Interpreter

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

private theorem dialect_zero : D.zero = (0 : U256) := rfl

private def addMaskedModDecl : FDecl D where
  params := ["dst", "src", "take", "modulus", "n"]
  rets := []
  body := yul% {
    let mask := sub(0, take)
    let carry := 0
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let off := mul(i, 32)
      let x := mload(add(dst, off))
      let y := and(mload(add(src, off)), mask)
      let s := add(x, y)
      let carry1 := lt(s, x)
      let z := add(s, carry)
      let carry2 := lt(z, s)
      mstore(add(dst, off), z)
      carry := or(carry1, carry2)
    }

    let borrow := 0
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let off := mul(i, 32)
      let x := mload(add(dst, off))
      let y := mload(add(modulus, off))
      let d := sub(x, y)
      let borrow1 := lt(x, y)
      let z := sub(d, borrow)
      let borrow2 := lt(d, borrow)
      mstore(add(0x1400, off), z)
      borrow := or(borrow1, borrow2)
    }

    let useSub := or(carry, iszero(borrow))
    let selectMask := sub(0, useSub)
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let off := mul(i, 32)
      let sum := mload(add(dst, off))
      let reduced := mload(add(0x1400, off))
      mstore(add(dst, off),
        or(and(reduced, selectMask), and(sum, not(selectMask))))
    }
  }

private theorem lookup_addMaskedMod :
    lookupFun verifiedFunctions "addMaskedMod" =
      some (addMaskedModDecl, verifiedFunctions) := by
  rfl

private def increment : Block Op := yul% { i := add(i, 1) }

private theorem ofNat_succ (i : Nat) :
    BitVec.ofNat 256 i + 1 = BitVec.ofNat 256 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

private def params (dst src take modulus n : U256) : VEnv D :=
  [("dst", dst), ("src", src), ("take", take), ("modulus", modulus), ("n", n)]

private def addEnv (dst src take modulus n mask : U256)
    (i : Nat) (carry : U256) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("carry", carry), ("mask", mask)] ++
    params dst src take modulus n

private def subEnv (dst src take modulus n mask carry : U256)
    (i : Nat) (borrow : U256) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("borrow", borrow), ("carry", carry),
    ("mask", mask)] ++ params dst src take modulus n

private def selectEnv (dst src take modulus n mask carry borrow useSub
    selectMask : U256) (i : Nat) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("selectMask", selectMask),
    ("useSub", useSub), ("borrow", borrow), ("carry", carry),
    ("mask", mask)] ++ params dst src take modulus n

def carryWord (smaller larger : U256) : U256 :=
  YulSemantics.EVM.b2w (BitVec.ult smaller larger)

structure AddPhase where
  state : EvmState
  carry : U256

def addStep (dst src mask : U256) (i : Nat)
    (phase : AddPhase) : AddPhase :=
  let dstAt := wordOffset dst i
  let srcAt := wordOffset src i
  let x := loadWord phase.state.memory dstAt.toNat
  let afterDst := touchMemory phase.state dstAt.toNat 32
  let y := loadWord afterDst.memory srcAt.toNat &&& mask
  let afterSrc := touchMemory afterDst srcAt.toNat 32
  let sum := x + y
  let carry1 := carryWord sum x
  let z := sum + phase.carry
  let carry2 := carryWord z sum
  { state := storeWordAt afterSrc dstAt z, carry := carry1 ||| carry2 }

def addPhase (st : EvmState) (dst src mask : U256) : Nat → AddPhase
  | 0 => ⟨st, 0⟩
  | i + 1 => addStep dst src mask i (addPhase st dst src mask i)

structure SubPhase where
  state : EvmState
  borrow : U256

def subStep (dst modulus : U256) (i : Nat)
    (phase : SubPhase) : SubPhase :=
  let dstAt := wordOffset dst i
  let modulusAt := wordOffset modulus i
  let candidateAt := wordOffset 0x1400 i
  let x := loadWord phase.state.memory dstAt.toNat
  let afterDst := touchMemory phase.state dstAt.toNat 32
  let y := loadWord afterDst.memory modulusAt.toNat
  let afterModulus := touchMemory afterDst modulusAt.toNat 32
  let difference := x - y
  let borrow1 := carryWord x y
  let z := difference - phase.borrow
  let borrow2 := carryWord difference phase.borrow
  { state := storeWordAt afterModulus candidateAt z,
    borrow := borrow1 ||| borrow2 }

def subPhase (st : EvmState) (dst modulus : U256) : Nat → SubPhase
  | 0 => ⟨st, 0⟩
  | i + 1 => subStep dst modulus i (subPhase st dst modulus i)

def selectStep (dst selectMask : U256) (i : Nat)
    (st : EvmState) : EvmState :=
  let dstAt := wordOffset dst i
  let candidateAt := wordOffset 0x1400 i
  let sum := loadWord st.memory dstAt.toNat
  let afterSum := touchMemory st dstAt.toNat 32
  let reduced := loadWord afterSum.memory candidateAt.toNat
  let afterReduced := touchMemory afterSum candidateAt.toNat 32
  let chosen := (reduced &&& selectMask) ||| (sum &&& ~~~selectMask)
  storeWordAt afterReduced dstAt chosen

def selectPhase (st : EvmState) (dst selectMask : U256) : Nat → EvmState
  | 0 => st
  | i + 1 => selectStep dst selectMask i (selectPhase st dst selectMask i)

/-- Exact post-state of the source `addMaskedMod` helper. -/
def addMaskedModState (st : EvmState) (dst src take modulus : U256)
    (count : Nat) : EvmState :=
  let mask := 0 - take
  let added := addPhase st dst src mask count
  let subtracted := subPhase added.state dst modulus count
  let useSub := added.carry ||| YulSemantics.EVM.b2w (subtracted.borrow = 0)
  selectPhase subtracted.state dst (0 - useSub) count

private def addBody : Block Op := yul% {
  let off := mul(i, 32)
  let x := mload(add(dst, off))
  let y := and(mload(add(src, off)), mask)
  let s := add(x, y)
  let carry1 := lt(s, x)
  let z := add(s, carry)
  let carry2 := lt(z, s)
  mstore(add(dst, off), z)
  carry := or(carry1, carry2)
}

private def subBody : Block Op := yul% {
  let off := mul(i, 32)
  let x := mload(add(dst, off))
  let y := mload(add(modulus, off))
  let d := sub(x, y)
  let borrow1 := lt(x, y)
  let z := sub(d, borrow)
  let borrow2 := lt(d, borrow)
  mstore(add(0x1400, off), z)
  borrow := or(borrow1, borrow2)
}

private def selectBody : Block Op := yul% {
  let off := mul(i, 32)
  let sum := mload(add(dst, off))
  let reduced := mload(add(0x1400, off))
  mstore(add(dst, off),
    or(and(reduced, selectMask), and(sum, not(selectMask))))
}

private theorem exec_addBody {funs : FunEnv D} (phase : AddPhase)
    (dst src take modulus n mask : U256) (i : Nat) :
    ExecStmt D funs (addEnv dst src take modulus n mask i phase.carry)
      phase.state (.block addBody)
      (addEnv dst src take modulus n mask i (addStep dst src mask i phase).carry)
      (addStep dst src mask i phase).state .normal := by
  have h : ExecStmt D funs
      (addEnv dst src take modulus n mask i phase.carry) phase.state
      (.block addBody)
      (addEnv dst src take modulus n mask i
        (addStep dst src mask i phase).carry)
      (addStep dst src mask i phase).state .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 180)
    rfl
  exact h

private theorem exec_subBody {funs : FunEnv D} (phase : SubPhase)
    (dst src take modulus n mask carry : U256) (i : Nat) :
    ExecStmt D funs
      (subEnv dst src take modulus n mask carry i phase.borrow)
      phase.state (.block subBody)
      (subEnv dst src take modulus n mask carry i
        (subStep dst modulus i phase).borrow)
      (subStep dst modulus i phase).state .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 180)
  rfl

private theorem exec_selectBody {funs : FunEnv D} (st : EvmState)
    (dst src take modulus n mask carry borrow useSub selectMask : U256)
    (i : Nat) :
    ExecStmt D funs
      (selectEnv dst src take modulus n mask carry borrow useSub selectMask i)
      st (.block selectBody)
      (selectEnv dst src take modulus n mask carry borrow useSub selectMask i)
      (selectStep dst selectMask i st) .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 150)
  rfl

private theorem exec_addIncrement {funs : FunEnv D} (st : EvmState)
    (dst src take modulus n mask carry : U256) (i : Nat) :
    ExecStmt D funs (addEnv dst src take modulus n mask i carry) st
      (.block increment) (addEnv dst src take modulus n mask (i + 1) carry)
      st .normal := by
  have h : ExecStmt D funs (addEnv dst src take modulus n mask i carry) st
      (.block increment)
      (("i", BitVec.ofNat 256 i + 1) ::
        [("carry", carry), ("mask", mask)] ++ params dst src take modulus n)
      st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ] at h
  simpa [addEnv] using h

private theorem exec_subIncrement {funs : FunEnv D} (st : EvmState)
    (dst src take modulus n mask carry borrow : U256) (i : Nat) :
    ExecStmt D funs (subEnv dst src take modulus n mask carry i borrow) st
      (.block increment)
      (subEnv dst src take modulus n mask carry (i + 1) borrow) st .normal := by
  have h : ExecStmt D funs (subEnv dst src take modulus n mask carry i borrow) st
      (.block increment)
      (("i", BitVec.ofNat 256 i + 1) ::
        [("borrow", borrow), ("carry", carry), ("mask", mask)] ++
          params dst src take modulus n) st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ] at h
  simpa [subEnv] using h

private theorem exec_selectIncrement {funs : FunEnv D} (st : EvmState)
    (dst src take modulus n mask carry borrow useSub selectMask : U256)
    (i : Nat) :
    ExecStmt D funs
      (selectEnv dst src take modulus n mask carry borrow useSub selectMask i) st
      (.block increment)
      (selectEnv dst src take modulus n mask carry borrow useSub selectMask (i + 1))
      st .normal := by
  have h : ExecStmt D funs
      (selectEnv dst src take modulus n mask carry borrow useSub selectMask i) st
      (.block increment)
      (("i", BitVec.ofNat 256 i + 1) ::
        [("selectMask", selectMask), ("useSub", useSub), ("borrow", borrow),
          ("carry", carry), ("mask", mask)] ++ params dst src take modulus n)
      st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ] at h
  simpa [selectEnv] using h

private theorem exec_addLoop {funs : FunEnv D} (st : EvmState)
    (dst src take modulus n mask : U256) :
    ∀ (k i : Nat), i + k = n.toNat →
      ExecLoop D funs
        (addEnv dst src take modulus n mask i
          (addPhase st dst src mask i).carry)
        (addPhase st dst src mask i).state
        (yulE% lt(i, n)) increment addBody
        (addEnv dst src take modulus n mask n.toNat
          (addPhase st dst src mask n.toNat).carry)
        (addPhase st dst src mask n.toNat).state .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = n.toNat := by omega
      subst i
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp only [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal]
      simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult]
  | succ k ih =>
      intro i hi
      have hin : i < n.toNat := by omega
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_addBody (addPhase st dst src mask i) dst src take modulus n mask i)
        (Or.inl rfl)
        (exec_addIncrement (addPhase st dst src mask (i + 1)).state
          dst src take modulus n mask
          (addStep dst src mask i (addPhase st dst src mask i)).carry i)
        ?_
      · simp only [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal]
        simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult,
          Nat.mod_eq_of_lt (hin.trans n.isLt), hin]
      · simpa [addPhase] using ih (i + 1) (by omega)

private theorem exec_subLoop {funs : FunEnv D} (st : EvmState)
    (dst src take modulus n mask carry : U256) :
    ∀ (k i : Nat), i + k = n.toNat →
      ExecLoop D funs
        (subEnv dst src take modulus n mask carry i
          (subPhase st dst modulus i).borrow)
        (subPhase st dst modulus i).state
        (yulE% lt(i, n)) increment subBody
        (subEnv dst src take modulus n mask carry n.toNat
          (subPhase st dst modulus n.toNat).borrow)
        (subPhase st dst modulus n.toNat).state .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = n.toNat := by omega
      subst i
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp only [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal]
      simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult]
  | succ k ih =>
      intro i hi
      have hin : i < n.toNat := by omega
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_subBody (subPhase st dst modulus i) dst src take modulus n mask carry i)
        (Or.inl rfl)
        (exec_subIncrement (subPhase st dst modulus (i + 1)).state
          dst src take modulus n mask carry
          (subStep dst modulus i (subPhase st dst modulus i)).borrow i)
        ?_
      · simp only [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal]
        simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult,
          Nat.mod_eq_of_lt (hin.trans n.isLt), hin]
      · simpa [subPhase] using ih (i + 1) (by omega)

private theorem exec_selectLoop {funs : FunEnv D} (st : EvmState)
    (dst src take modulus n mask carry borrow useSub selectMask : U256) :
    ∀ (k i : Nat), i + k = n.toNat →
      ExecLoop D funs
        (selectEnv dst src take modulus n mask carry borrow useSub selectMask i)
        (selectPhase st dst selectMask i)
        (yulE% lt(i, n)) increment selectBody
        (selectEnv dst src take modulus n mask carry borrow useSub selectMask n.toNat)
        (selectPhase st dst selectMask n.toNat) .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = n.toNat := by omega
      subst i
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp only [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal]
      simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult]
  | succ k ih =>
      intro i hi
      have hin : i < n.toNat := by omega
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_selectBody (selectPhase st dst selectMask i)
          dst src take modulus n mask carry borrow useSub selectMask i)
        (Or.inl rfl)
        (exec_selectIncrement (selectPhase st dst selectMask (i + 1))
          dst src take modulus n mask carry borrow useSub selectMask i)
        ?_
      · simp only [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal]
        simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult,
          Nat.mod_eq_of_lt (hin.trans n.isLt), hin]
      · simpa [selectPhase] using ih (i + 1) (by omega)

private theorem exec_addMaskedModBody (st : EvmState)
    (dst src take modulus n : U256) :
    ExecStmt D verifiedFunctions (params dst src take modulus n) st
      (.block addMaskedModDecl.body) (params dst src take modulus n)
      (addMaskedModState st dst src take modulus n.toNat) .normal := by
  let mask : U256 := 0 - take
  let added := addPhase st dst src mask n.toNat
  let subtracted := subPhase added.state dst modulus n.toNat
  let useSub : U256 := added.carry |||
    YulSemantics.EVM.b2w (subtracted.borrow = 0)
  let selectMask : U256 := 0 - useSub
  let bodyFuns : FunEnv D := hoist D addMaskedModDecl.body :: verifiedFunctions
  have hmask : EvalExpr D bodyFuns (params dst src take modulus n) st
      (yulE% sub(0, take)) (.vals [mask] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  have huseSub : EvalExpr D bodyFuns
      ([("borrow", subtracted.borrow), ("carry", added.carry), ("mask", mask)] ++
        params dst src take modulus n)
      subtracted.state (yulE% or(carry, iszero(borrow)))
      (.vals [useSub] subtracted.state) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 40)
    rfl
  have hselectMask : EvalExpr D bodyFuns
      ([("useSub", useSub), ("borrow", subtracted.borrow),
        ("carry", added.carry), ("mask", mask)] ++ params dst src take modulus n)
      subtracted.state (yulE% sub(0, useSub))
      (.vals [selectMask] subtracted.state) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  refine Step.block (D := D)
    (Vb := [("selectMask", selectMask), ("useSub", useSub),
      ("borrow", subtracted.borrow), ("carry", added.carry),
      ("mask", mask)] ++ params dst src take modulus n)
    (stb := selectPhase subtracted.state dst selectMask n.toNat) ?_
  refine Step.seqCons (Step.letVal hmask rfl) ?_
  refine Step.seqCons (Step.letVal Step.lit rfl) ?_
  simp only [D, Challenge.YulProof.ClosedEvm.dialect,
    YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.litValue,
    List.zip, List.zipWith, List.append]
  refine Step.seqCons
    (V1 := [("carry", added.carry), ("mask", mask)] ++
      params dst src take modulus n)
    (st1 := added.state) ?_ ?_
  · refine Step.forLoop (D := D)
      (Vinit := addEnv dst src take modulus n mask 0 0)
      (stinit := st)
      (Vend := addEnv dst src take modulus n mask n.toNat added.carry) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa [bodyFuns, addMaskedModDecl, addEnv, addBody, increment,
        addPhase, added, hoist] using
        exec_addLoop
          (funs := hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] ::
            bodyFuns)
          st dst src take modulus n mask n.toNat 0 (by omega)
  · refine Step.seqCons (Step.letVal Step.lit rfl) ?_
    simp only [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.litValue,
      List.zip, List.zipWith, List.append]
    refine Step.seqCons
      (V1 := [("borrow", subtracted.borrow), ("carry", added.carry),
        ("mask", mask)] ++ params dst src take modulus n)
      (st1 := subtracted.state) ?_ ?_
    · refine Step.forLoop (D := D)
        (Vinit := subEnv dst src take modulus n mask added.carry 0 0)
        (stinit := added.state)
        (Vend := subEnv dst src take modulus n mask added.carry n.toNat
          subtracted.borrow) ?_ ?_
      · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
      · simpa [bodyFuns, addMaskedModDecl, subEnv, subBody, increment,
          subPhase, subtracted, hoist] using
          exec_subLoop
            (funs := hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] ::
              bodyFuns)
            added.state dst src take modulus n mask added.carry n.toNat 0 (by omega)
    · refine Step.seqCons (Step.letVal huseSub rfl) ?_
      refine Step.seqCons (Step.letVal hselectMask rfl) ?_
      refine Step.seqCons (D := D)
        (V1 := [("selectMask", selectMask), ("useSub", useSub),
          ("borrow", subtracted.borrow), ("carry", added.carry),
          ("mask", mask)] ++ params dst src take modulus n)
        (st1 := selectPhase subtracted.state dst selectMask n.toNat)
        ?_ (Step.seqNil (D := D))
      refine Step.forLoop (D := D)
        (Vinit := selectEnv dst src take modulus n mask added.carry
          subtracted.borrow useSub selectMask 0)
        (stinit := subtracted.state)
        (Vend := selectEnv dst src take modulus n mask added.carry
          subtracted.borrow useSub selectMask n.toNat) ?_ ?_
      · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
      · simpa [bodyFuns, addMaskedModDecl, selectEnv, selectBody, increment,
          selectPhase, hoist] using
          exec_selectLoop
            (funs := hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] ::
              bodyFuns)
            subtracted.state dst src take modulus n mask added.carry
            subtracted.borrow useSub selectMask n.toNat 0 (by omega)

/-- Direct relational contract for the source `addMaskedMod` helper. -/
theorem eval_addMaskedMod {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)}
    (dst src take modulus n : U256)
    (hlookup : lookupFun funs "addMaskedMod" =
      some (addMaskedModDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args
      (.vals [dst, src, take, modulus, n] st1)) :
    EvalExpr D funs V st (.call "addMaskedMod" args)
      (.vals [] (addMaskedModState st1 dst src take modulus n.toNat)) := by
  refine Step.callOk (D := D) (Vend := params dst src take modulus n)
    hargs hlookup rfl (exec_addMaskedModBody st1 dst src take modulus n)
    (Or.inl rfl)

/-- Lookup-specialized `addMaskedMod` contract for the verified program. -/
theorem eval_addMaskedMod_verified {V : VEnv D} {st st1 : EvmState}
    {args : List (Expr Op)} (dst src take modulus n : U256)
    (hargs : EvalArgs D verifiedFunctions V st args
      (.vals [dst, src, take, modulus, n] st1)) :
    EvalExpr D verifiedFunctions V st (.call "addMaskedMod" args)
      (.vals [] (addMaskedModState st1 dst src take modulus n.toNat)) :=
  eval_addMaskedMod dst src take modulus n lookup_addMaskedMod hargs

end Challenge.Modexp.Reference.Proofs.Yul.BigArithmetic
