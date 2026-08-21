import Challenge.Modexp.Reference.Proofs.Yul.StateModel
import Challenge.YulProof.EvmState
import Challenge.YulProof.Interpreter

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Relational contracts for MODEXP big-path data movement

This file proves the source Yul loops which load a big-endian byte string into
little-endian 256-bit limbs and serialize the final limbs back to bytes.  The
contracts expose exact `EvmState` transformers, while the arithmetic indexing
facts are shared with the certified bytecode development.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul

open YulSemantics
open YulSemantics.EVM
open StateModel
open Challenge.YulProof.EvmState
open Challenge.YulProof.Interpreter

private abbrev D := Challenge.YulProof.ClosedEvm.dialect
private abbrev E := Challenge.YulProof.ClosedEvm.exec

private def calldataByteDecl : FDecl D where
  params := ["off"]
  rets := ["b"]
  body := yul% { b := byte(0, calldataload(off)) }

private def loadBigEndianDecl : FDecl D where
  params := ["off", "len", "dst"]
  rets := []
  body := yul% {
    for { let i := 0 } lt(i, len) { i := add(i, 1) } {
      let reverse := sub(sub(len, 1), i)
      let limb := div(reverse, 32)
      let shift := mul(mod(reverse, 32), 8)
      let dstAt := add(dst, mul(limb, 32))
      mstore(dstAt, or(mload(dstAt), shl(shift, calldataByte(add(off, i)))))
    }
  }

private theorem lookup_loadBigEndian :
    lookupFun verifiedFunctions "loadBigEndian" =
      some (loadBigEndianDecl, verifiedFunctions) := by
  rfl

private theorem lookup_calldataByte :
    lookupFun verifiedFunctions "calldataByte" =
      some (calldataByteDecl, verifiedFunctions) := by
  rfl

private theorem exec_calldataByteBody (st : EvmState) (off : U256) :
    ExecStmt D verifiedFunctions [("off", off), ("b", 0)] st
      (.block calldataByteDecl.body)
      [("off", off), ("b", calldataByteValue st off)] st .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
  rfl

private theorem eval_calldataByte {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {arg : Expr Op} (off : U256)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions))
    (harg : EvalExpr D funs V st arg (.vals [off] st1)) :
    EvalExpr D funs V st (.call "calldataByte" [arg])
      (.vals [calldataByteValue st1 off] st1) := by
  refine Step.callOk (D := D)
    (Step.argsCons Step.argsNil harg) hlookup rfl
    (exec_calldataByteBody st1 off) (Or.inl rfl)

/-- Destination limb selected by source `loadBigEndian` at iteration `i`. -/
def loadLimbAddress (len dst : U256) (i : Nat) : U256 :=
  let reverse := len - 1 - BitVec.ofNat 256 i
  dst + (reverse / 32) * 32

/-- Source shift selected by `loadBigEndian` at iteration `i`. -/
def loadByteShift (len : U256) (i : Nat) : Nat :=
  (((len - 1 - BitVec.ofNat 256 i) % 32) * 8).toNat

/-- One exact source iteration, including the `mload` and `mstore` memory
touches. -/
def loadBigEndianStep (current : EvmState) (off len dst : U256)
    (i : Nat) : EvmState :=
  let p := loadLimbAddress len dst i
  let loaded := touchMemory current p.toNat 32
  let byte :=
    (wordFrom current.env.calldata
      (off + BitVec.ofNat 256 i).toNat >>> 248) &&& 0xff
  let value := loadWord current.memory p.toNat ||| (byte <<< loadByteShift len i)
  { touchMemory loaded p.toNat 32 with
    memory := storeWord loaded.memory p.toNat value }

/-- State after loading the first `i` bytes. -/
def loadBigEndianPrefix (original : EvmState) (off len dst : U256) :
    Nat → EvmState
  | 0 => original
  | i + 1 =>
      loadBigEndianStep (loadBigEndianPrefix original off len dst i)
        off len dst i

private def loadBody : Block Op := yul% {
  let reverse := sub(sub(len, 1), i)
  let limb := div(reverse, 32)
  let shift := mul(mod(reverse, 32), 8)
  let dstAt := add(dst, mul(limb, 32))
  mstore(dstAt, or(mload(dstAt), shl(shift, calldataByte(add(off, i)))))
}

def incrementI : Block Op := yul% { i := add(i, 1) }

private theorem ofNat_succ (i : Nat) :
    BitVec.ofNat 256 i + 1 = BitVec.ofNat 256 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

private def loadTail (off len dst : U256) : VEnv D :=
  [("off", off), ("len", len), ("dst", dst)]

private theorem exec_loadBigEndianBody (st : EvmState) (off len dst : U256) :
    ExecStmt D verifiedFunctions (loadTail off len dst) st
      (.block loadBigEndianDecl.body) (loadTail off len dst)
      (loadBigEndianPrefix st off len dst len.toNat) .normal := by
  let Vtail := loadTail off len dst
  let bodyFuns : FunEnv D := [] :: verifiedFunctions
  let loopFuns : FunEnv D := [] :: bodyFuns
  have hcond (i : Nat) (_hi : i ≤ len.toNat) (current : EvmState) :
      EvalExpr D loopFuns (("i", BitVec.ofNat 256 i) :: Vtail) current
        (yulE% lt(i, len))
        (.vals [if i < len.toNat then (1 : U256) else 0] current) := by
    refine Step.builtinOk (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) ?_
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin,
      YulSemantics.EVM.b2w, YulSemantics.EVM.litValue, BitVec.ult,
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
    simp only [show 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2 ^ 256 by norm_num, Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
    split <;> rfl
  have hbody (i : Nat) (hi : i < len.toNat) (current : EvmState) :
      ExecStmt D loopFuns (("i", BitVec.ofNat 256 i) :: Vtail) current
        (.block loadBody) (("i", BitVec.ofNat 256 i) :: Vtail)
        (loadBigEndianStep current off len dst i) .normal := by
    let reverse := len - 1 - BitVec.ofNat 256 i
    let limb := reverse / 32
    let shift := (reverse % 32) * 8
    let p := dst + limb * 32
    let V0 := ("i", BitVec.ofNat 256 i) :: Vtail
    let V1 := ("reverse", reverse) :: V0
    let V2 := ("limb", limb) :: V1
    let V3 := ("shift", shift) :: V2
    let V4 := ("dstAt", p) :: V3
    let innerFuns : FunEnv D := hoist D loadBody :: loopFuns
    have hreverse : EvalExpr D innerFuns V0 current
        (yulE% sub(sub(len, 1), i)) (.vals [reverse] current) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
      rfl
    have hlimb : EvalExpr D innerFuns V1 current
        (yulE% div(reverse, 32)) (.vals [limb] current) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
      rfl
    have hshift : EvalExpr D innerFuns V2 current
        (yulE% mul(mod(reverse, 32), 8)) (.vals [shift] current) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
      rfl
    have hp : EvalExpr D innerFuns V3 current
        (yulE% add(dst, mul(limb, 32))) (.vals [p] current) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
      rfl
    have hoff : EvalExpr D innerFuns V4 current (yulE% add(off, i))
        (.vals [off + BitVec.ofNat 256 i] current) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
      rfl
    have hlookup : lookupFun innerFuns "calldataByte" =
        some (calldataByteDecl, verifiedFunctions) := by
      simpa [innerFuns, loopFuns, bodyFuns, loadBody, hoist, lookupFun]
        using lookup_calldataByte
    have hbyte := eval_calldataByte (off + BitVec.ofNat 256 i) hlookup hoff
    have hshifted : EvalExpr D innerFuns V4 current
        (yulE% shl(shift, calldataByte(add(off, i))))
        (.vals [calldataByteValue current (off + BitVec.ofNat 256 i) <<< shift.toNat]
          current) := by
      exact Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil hbyte) (Step.var rfl)) rfl
    let loaded := touchMemory current p.toNat 32
    have hload : EvalExpr D innerFuns V4 current (yulE% mload(dstAt))
        (.vals [loadWord current.memory p.toNat] loaded) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
      rfl
    let value := loadWord current.memory p.toNat |||
      (calldataByteValue current (off + BitVec.ofNat 256 i) <<< shift.toNat)
    have hor : EvalExpr D innerFuns V4 current
        (yulE% or(mload(dstAt), shl(shift, calldataByte(add(off, i)))))
        (.vals [value] loaded) := by
      exact Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil hshifted) hload) rfl
    have hmstore : EvalExpr D innerFuns V4 current
        (yulE% mstore(dstAt,
          or(mload(dstAt), shl(shift, calldataByte(add(off, i))))))
        (.vals [] (loadBigEndianStep current off len dst i)) := by
      have hargs : EvalArgs D innerFuns V4 current
          [yulE% dstAt,
            yulE% or(mload(dstAt), shl(shift, calldataByte(add(off, i))))]
          (.vals [p, value] loaded) :=
        Step.argsCons (Step.argsCons Step.argsNil hor) (Step.var rfl)
      refine Step.builtinOk hargs ?_
      simp [loadBigEndianStep, loadLimbAddress, loadByteShift, reverse, limb,
        shift, p, loaded, value, calldataByteValue,
        D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.stepOp]
    have hseq : ExecStmts D innerFuns V0 current loadBody V4
        (loadBigEndianStep current off len dst i) .normal := by
      refine Step.seqCons (Step.letVal hreverse rfl) ?_
      refine Step.seqCons (Step.letVal hlimb rfl) ?_
      refine Step.seqCons (Step.letVal hshift rfl) ?_
      refine Step.seqCons (Step.letVal hp rfl) ?_
      refine Step.seqCons (Step.exprStmt hmstore) Step.seqNil
    have hblock := Step.block (D := D) hseq
    simpa [innerFuns, V0, V1, V2, V3, V4, loadBody, restore] using hblock
  have hpost (i : Nat) (hi : i < len.toNat) (current : EvmState) :
      ExecStmt D loopFuns (("i", BitVec.ofNat 256 i) :: Vtail) current
        (.block incrementI) (("i", BitVec.ofNat 256 (i + 1)) :: Vtail)
        current .normal := by
    let innerFuns : FunEnv D := hoist D incrementI :: loopFuns
    have hadd : EvalExpr D innerFuns
        (("i", BitVec.ofNat 256 i) :: Vtail) current (yulE% add(i, 1))
        (.vals [BitVec.ofNat 256 (i + 1)] current) := by
      have hraw : EvalExpr D innerFuns
          (("i", BitVec.ofNat 256 i) :: Vtail) current (yulE% add(i, 1))
          (.vals [BitVec.ofNat 256 i + 1] current) :=
        Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl
      rw [ofNat_succ] at hraw
      exact hraw
    have hassign := Step.assignVal (D := D) (vars := ["i"]) hadd rfl
    have hset : VEnv.setMany (("i", BitVec.ofNat 256 i) :: Vtail)
        ["i"] [BitVec.ofNat 256 (i + 1)] =
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail := by
      rfl
    rw [hset] at hassign
    have hseq := Step.seqCons (D := D) hassign (Step.seqNil (D := D))
    have hblock := Step.block (D := D) hseq
    simpa [innerFuns, incrementI, restore] using hblock
  simp only [loadBigEndianDecl]
  refine Step.block (D := D) (Vb := loadTail off len dst) ?_
  refine Step.seqCons (D := D) ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := ("i", 0) :: Vtail) (stinit := st)
    (Vend := ("i", BitVec.ofNat 256 len.toNat) :: Vtail) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · let Inv : Nat → VEnv D → EvmState → Prop :=
      fun remaining V current => ∃ i,
        i + remaining = len.toNat ∧
        V = ("i", BitVec.ofNat 256 i) :: Vtail ∧
        current = loadBigEndianPrefix st off len dst i
    have hdone : ∀ V current, Inv 0 V current →
        ∃ cv current', EvalExpr D loopFuns V current (yulE% lt(i, len))
          (.vals [cv] current') ∧ cv = 0 ∧ Inv 0 V current' := by
      intro V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hiEq : i = len.toNat := by omega
      subst i
      exact ⟨0, _, by simpa using hcond len.toNat (by omega) _, rfl,
        len.toNat, by omega, rfl, rfl⟩
    have hstep : ∀ remaining V current, Inv (remaining + 1) V current →
        ∃ cv currentCond Vb currentBody ob Vp currentPost,
          EvalExpr D loopFuns V current (yulE% lt(i, len))
            (.vals [cv] currentCond) ∧ cv ≠ 0 ∧
          ExecStmt D loopFuns V currentCond (.block loadBody)
            Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
          ExecStmt D loopFuns Vb currentBody (.block incrementI)
            Vp currentPost .normal ∧ Inv remaining Vp currentPost := by
      intro remaining V current hInv
      obtain ⟨i, hi, rfl, rfl⟩ := hInv
      have hilt : i < len.toNat := by omega
      refine ⟨(1 : U256), loadBigEndianPrefix st off len dst i,
        ("i", BitVec.ofNat 256 i) :: Vtail,
        loadBigEndianPrefix st off len dst (i + 1), .normal,
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail,
        loadBigEndianPrefix st off len dst (i + 1), ?_, by decide, ?_,
        Or.inl rfl, ?_, ?_⟩
      · simpa [hilt] using hcond i (by omega)
          (loadBigEndianPrefix st off len dst i)
      · simpa [loadBigEndianPrefix] using hbody i hilt
          (loadBigEndianPrefix st off len dst i)
      · exact hpost i hilt _
      · exact ⟨i + 1, by omega, rfl, rfl⟩
    obtain ⟨V', current', hloop, hInv⟩ :=
      ExecLoop.countdown (D := D) (funs := loopFuns)
        (cond := yulE% lt(i, len)) (post := incrementI) (body := loadBody)
        (Inv := Inv) hdone hstep len.toNat (("i", 0) :: Vtail) st
        ⟨0, by omega, rfl, rfl⟩
    obtain ⟨i, hi, hV, hstate⟩ := hInv
    have hiEq : i = len.toNat := by omega
    subst i
    subst V'
    subst current'
    simpa [loopFuns, bodyFuns, loadBody, incrementI, Vtail,
      loadBigEndianDecl, hoist] using hloop

/-- Direct relational contract for source `loadBigEndian`. -/
theorem eval_loadBigEndian {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)} (off len dst : U256)
    (hlookup : lookupFun funs "loadBigEndian" =
      some (loadBigEndianDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args (.vals [off, len, dst] st1)) :
    EvalExpr D funs V st (.call "loadBigEndian" args)
      (.vals [] (loadBigEndianPrefix st1 off len dst len.toNat)) := by
  exact Step.callOk (D := D) hargs hlookup rfl
    (exec_loadBigEndianBody st1 off len dst) (Or.inl rfl)

/-! ## Modulus nonzero scan -/

/-- State after the first `i` modulus-limb reads. -/
def modulusScanPrefix : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st =>
      let before := modulusScanPrefix i st
      touchMemory before (BitVec.ofNat 256 i * (32 : U256)).toNat 32

/-- Bitwise OR of the first `i` modulus limbs, in the states in which the Yul
loop reads them. -/
def modulusOrPrefix : Nat → EvmState → U256
  | 0, _ => 0
  | i + 1, st =>
      let before := modulusScanPrefix i st
      modulusOrPrefix i st |||
        loadWord before.memory (BitVec.ofNat 256 i * (32 : U256)).toNat

def modulusScanBody : Block Op := yul% {
  modulusOr := or(modulusOr, mload(mul(i, 32)))
}

def scanEnv (n : U256) (tail : VEnv D) (i : Nat) (acc : U256) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("modulusOr", acc), ("n", n)] ++ tail

private theorem exec_modulusScanBody {funs : FunEnv D} (tail : VEnv D)
    (st : EvmState) (n : U256) (i : Nat) :
    ExecStmt D funs (scanEnv n tail i (modulusOrPrefix i st))
      (modulusScanPrefix i st) (.block modulusScanBody)
      (scanEnv n tail i (modulusOrPrefix (i + 1) st))
      (modulusScanPrefix (i + 1) st) .normal := by
  let current := modulusScanPrefix i st
  let next := modulusScanPrefix (i + 1) st
  let acc := modulusOrPrefix i st
  let nextAcc := modulusOrPrefix (i + 1) st
  let p := BitVec.ofNat 256 i * (32 : U256)
  let V0 := scanEnv n tail i acc
  let innerFuns : FunEnv D := hoist D modulusScanBody :: funs
  have hp : EvalExpr D innerFuns V0 current (yulE% mul(i, 32))
      (.vals [p] current) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl
  have hload : EvalExpr D innerFuns V0 current (yulE% mload(mul(i, 32)))
      (.vals [loadWord current.memory p.toNat] next) := by
    refine Step.builtinOk (Step.argsCons Step.argsNil hp) ?_
    simp [current, next, p, modulusScanPrefix,
      D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp]
  have hacc : EvalExpr D innerFuns V0 next (yulE% modulusOr)
      (.vals [acc] next) := Step.var (by rfl)
  have hor : EvalExpr D innerFuns V0 current
      (yulE% or(modulusOr, mload(mul(i, 32)))) (.vals [nextAcc] next) := by
    have hraw : EvalExpr D innerFuns V0 current
        (yulE% or(modulusOr, mload(mul(i, 32))))
        (.vals [acc ||| loadWord current.memory p.toNat] next) :=
      Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hload) hacc) rfl
    simpa [acc, nextAcc, current, p, modulusOrPrefix] using hraw
  have hassign := Step.assignVal (D := D) (vars := ["modulusOr"]) hor rfl
  have hset : VEnv.setMany V0 ["modulusOr"] [nextAcc] =
      scanEnv n tail i nextAcc := by rfl
  rw [hset] at hassign
  have hseq := Step.seqCons (D := D) hassign (Step.seqNil (D := D))
  have hblock := Step.block (D := D) hseq
  have hrestore :
      restore (scanEnv n tail i acc) (scanEnv n tail i nextAcc) =
        scanEnv n tail i nextAcc := by
    simp [restore, scanEnv]
  simpa [innerFuns, modulusScanBody, V0, current, next, acc, nextAcc,
    hrestore] using hblock

/-- Direct contract for the source loop which detects a zero big modulus. -/
theorem exec_modulusScanLoop {funs : FunEnv D} (tail : VEnv D)
    (st : EvmState) (n : U256) :
    ExecLoop D funs (scanEnv n tail 0 0) st (yulE% lt(i, n))
      incrementI modulusScanBody
      (scanEnv n tail n.toNat (modulusOrPrefix n.toNat st))
      (modulusScanPrefix n.toNat st) .normal := by
  have hpost (i : Nat) (acc : U256) (current : EvmState) :
      ExecStmt D funs (scanEnv n tail i acc) current (.block incrementI)
        (scanEnv n tail (i + 1) acc) current .normal := by
    let Vtail : VEnv D := [("modulusOr", acc), ("n", n)] ++ tail
    let innerFuns : FunEnv D := hoist D incrementI :: funs
    have hadd : EvalExpr D innerFuns (("i", BitVec.ofNat 256 i) :: Vtail)
        current (yulE% add(i, 1))
        (.vals [BitVec.ofNat 256 (i + 1)] current) := by
      have hraw : EvalExpr D innerFuns (("i", BitVec.ofNat 256 i) :: Vtail)
          current (yulE% add(i, 1))
          (.vals [BitVec.ofNat 256 i + 1] current) :=
        Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl
      rw [ofNat_succ] at hraw
      exact hraw
    have hassign := Step.assignVal (D := D) (vars := ["i"]) hadd rfl
    have hset : VEnv.setMany (("i", BitVec.ofNat 256 i) :: Vtail)
        ["i"] [BitVec.ofNat 256 (i + 1)] =
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail := by rfl
    rw [hset] at hassign
    have hseq := Step.seqCons (D := D) hassign (Step.seqNil (D := D))
    have hblock := Step.block (D := D) hseq
    simpa [innerFuns, incrementI, scanEnv, Vtail, restore] using hblock
  have hcond (i : Nat) (_hi : i ≤ n.toNat) (acc : U256) (current : EvmState) :
      EvalExpr D funs (scanEnv n tail i acc) current (yulE% lt(i, n))
        (.vals [if i < n.toNat then (1 : U256) else 0] current) := by
    refine Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) ?_
    simp [scanEnv, D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin,
      YulSemantics.EVM.b2w, YulSemantics.EVM.litValue, BitVec.ult]
    simp only [show 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2 ^ 256 by norm_num, Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
    split <;> rfl
  let Inv : Nat → VEnv D → EvmState → Prop :=
    fun remaining V current => ∃ i,
      i + remaining = n.toNat ∧
      V = scanEnv n tail i (modulusOrPrefix i st) ∧
      current = modulusScanPrefix i st
  have hdone : ∀ V current, Inv 0 V current →
      ∃ cv current', EvalExpr D funs V current (yulE% lt(i, n))
        (.vals [cv] current') ∧ cv = 0 ∧ Inv 0 V current' := by
    intro V current hInv
    obtain ⟨i, hi, rfl, rfl⟩ := hInv
    have hiEq : i = n.toNat := by omega
    subst i
    have hc := hcond n.toNat (by omega) (modulusOrPrefix n.toNat st)
      (modulusScanPrefix n.toNat st)
    exact ⟨0, _, by simpa using hc, rfl, n.toNat, by omega, rfl, rfl⟩
  have hstep : ∀ remaining V current, Inv (remaining + 1) V current →
      ∃ cv currentCond Vb currentBody ob Vp currentPost,
        EvalExpr D funs V current (yulE% lt(i, n))
          (.vals [cv] currentCond) ∧ cv ≠ 0 ∧
        ExecStmt D funs V currentCond (.block modulusScanBody)
          Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
        ExecStmt D funs Vb currentBody (.block incrementI)
          Vp currentPost .normal ∧ Inv remaining Vp currentPost := by
    intro remaining V current hInv
    obtain ⟨i, hi, rfl, rfl⟩ := hInv
    have hilt : i < n.toNat := by omega
    refine ⟨(1 : U256), modulusScanPrefix i st,
      scanEnv n tail i (modulusOrPrefix (i + 1) st),
      modulusScanPrefix (i + 1) st, .normal,
      scanEnv n tail (i + 1) (modulusOrPrefix (i + 1) st),
      modulusScanPrefix (i + 1) st, ?_, by decide, ?_, Or.inl rfl, ?_, ?_⟩
    · simpa [hilt] using hcond i (by omega) (modulusOrPrefix i st)
        (modulusScanPrefix i st)
    · exact exec_modulusScanBody tail st n i
    · exact hpost i (modulusOrPrefix (i + 1) st) _
    · exact ⟨i + 1, by omega, rfl, rfl⟩
  obtain ⟨V', current', hloop, hInv⟩ :=
    ExecLoop.countdown (D := D) (funs := funs) (cond := yulE% lt(i, n))
      (post := incrementI) (body := modulusScanBody) (Inv := Inv)
      hdone hstep n.toNat (scanEnv n tail 0 0) st
      ⟨0, by omega, rfl, rfl⟩
  obtain ⟨i, hi, hV, hstate⟩ := hInv
  have hiEq : i = n.toNat := by omega
  subst i
  subst V'
  subst current'
  simpa using hloop

/-! ## Final big-path byte serialization -/

/-- Limb read by the final serializer at byte index `i`. -/
def serializeLimbAddress (modulusSize : U256) (i : Nat) : U256 :=
  let reverse := modulusSize - 1 - BitVec.ofNat 256 i
  0x0800 + (reverse / 32) * 32

/-- Bit shift used by the final serializer at byte index `i`. -/
def serializeByteShift (modulusSize : U256) (i : Nat) : Nat :=
  ((((modulusSize - 1 - BitVec.ofNat 256 i) % 32) * 8 : U256)).toNat

/-- One exact final-serialization iteration. -/
def serializeStep (current : EvmState) (modulusSize : U256) (i : Nat) : EvmState :=
  let src := serializeLimbAddress modulusSize i
  let loaded := touchMemory current src.toNat 32
  let value := (loadWord current.memory src.toNat >>>
    serializeByteShift modulusSize i) &&& 0xff
  let dst : U256 := 0x1800 + BitVec.ofNat 256 i
  { touchMemory loaded dst.toNat 1 with
    memory := storeByte loaded.memory dst.toNat value }

/-- State after serializing the first `i` result bytes. -/
def serializePrefix (modulusSize : U256) : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st => serializeStep (serializePrefix modulusSize i st) modulusSize i

def serializeBody : Block Op := yul% {
  let reverse := sub(sub(modulusSize, 1), i)
  let limb := div(reverse, 32)
  let shift := mul(mod(reverse, 32), 8)
  mstore8(add(0x1800, i),
    and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff))
}

private theorem exec_serializeBody {funs : FunEnv D} (Vtail : VEnv D)
    (st : EvmState) (modulusSize : U256)
    (hmodulus : VEnv.get Vtail "modulusSize" = some modulusSize)
    (i : Nat) :
    ExecStmt D funs (("i", BitVec.ofNat 256 i) :: Vtail) st
      (.block serializeBody) (("i", BitVec.ofNat 256 i) :: Vtail)
      (serializeStep st modulusSize i) .normal := by
  let reverse := modulusSize - 1 - BitVec.ofNat 256 i
  let limb := reverse / 32
  let shift := (reverse % 32) * 8
  let src : U256 := 0x0800 + limb * 32
  let dst : U256 := 0x1800 + BitVec.ofNat 256 i
  let V0 := ("i", BitVec.ofNat 256 i) :: Vtail
  let V1 := ("reverse", reverse) :: V0
  let V2 := ("limb", limb) :: V1
  let V3 := ("shift", shift) :: V2
  let innerFuns : FunEnv D := hoist D serializeBody :: funs
  have hm : EvalExpr D innerFuns V0 st (yulE% modulusSize)
      (.vals [modulusSize] st) := by
    exact Step.var (by simpa [V0, VEnv.get] using hmodulus)
  have hm1 : EvalExpr D innerFuns V0 st (yulE% sub(modulusSize, 1))
      (.vals [modulusSize - 1] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hm) rfl
  have hreverse : EvalExpr D innerFuns V0 st
      (yulE% sub(sub(modulusSize, 1), i)) (.vals [reverse] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) hm1) rfl
  have hlimb : EvalExpr D innerFuns V1 st (yulE% div(reverse, 32))
      (.vals [limb] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl
  have hrem : EvalExpr D innerFuns V2 st (yulE% mod(reverse, 32))
      (.vals [reverse % 32] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl
  have hshift : EvalExpr D innerFuns V2 st (yulE% mul(mod(reverse, 32), 8))
      (.vals [shift] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hrem) rfl
  have hmul : EvalExpr D innerFuns V3 st (yulE% mul(limb, 32))
      (.vals [limb * 32] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl
  have hsrc : EvalExpr D innerFuns V3 st (yulE% add(0x0800, mul(limb, 32)))
      (.vals [src] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hmul) Step.lit) rfl
  let loaded := touchMemory st src.toNat 32
  have hload : EvalExpr D innerFuns V3 st
      (yulE% mload(add(0x0800, mul(limb, 32))))
      (.vals [loadWord st.memory src.toNat] loaded) :=
    Step.builtinOk (Step.argsCons Step.argsNil hsrc) rfl
  have hshr : EvalExpr D innerFuns V3 st
      (yulE% shr(shift, mload(add(0x0800, mul(limb, 32)))))
      (.vals [loadWord st.memory src.toNat >>> shift.toNat] loaded) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hload) (Step.var rfl)) rfl
  let value := (loadWord st.memory src.toNat >>> shift.toNat) &&& 0xff
  have hand : EvalExpr D innerFuns V3 st
      (yulE% and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff))
      (.vals [value] loaded) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hshr) rfl
  have hdst : EvalExpr D innerFuns V3 loaded (yulE% add(0x1800, i))
      (.vals [dst] loaded) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit) rfl
  have hstore : EvalExpr D innerFuns V3 st
      (yulE% mstore8(add(0x1800, i),
        and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff)))
      (.vals [] (serializeStep st modulusSize i)) := by
    have hargs : EvalArgs D innerFuns V3 st
        [yulE% add(0x1800, i),
          yulE% and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff)]
        (.vals [dst, value] loaded) :=
      Step.argsCons (Step.argsCons Step.argsNil hand) hdst
    refine Step.builtinOk hargs ?_
    simp [serializeStep, serializeLimbAddress, serializeByteShift,
      reverse, limb, shift, src, dst, loaded, value,
      D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp]
  have hseq : ExecStmts D innerFuns V0 st serializeBody V3
      (serializeStep st modulusSize i) .normal := by
    refine Step.seqCons (Step.letVal hreverse rfl) ?_
    refine Step.seqCons (Step.letVal hlimb rfl) ?_
    refine Step.seqCons (Step.letVal hshift rfl) ?_
    refine Step.seqCons (Step.exprStmt hstore) Step.seqNil
  have hblock := Step.block (D := D) hseq
  simpa [innerFuns, serializeBody, V0, V1, V2, V3, restore] using hblock

/-- Direct relational contract for the final source-level byte loop.  The
ambient environment is otherwise arbitrary; only its `modulusSize` binding is
observed. -/
theorem exec_serializeLoop {funs : FunEnv D} (Vtail : VEnv D) (st : EvmState)
    (modulusSize : U256)
    (hmodulus : VEnv.get Vtail "modulusSize" = some modulusSize) :
    ExecLoop D funs (("i", 0) :: Vtail) st
      (yulE% lt(i, modulusSize)) incrementI serializeBody
      (("i", BitVec.ofNat 256 modulusSize.toNat) :: Vtail)
      (serializePrefix modulusSize modulusSize.toNat st) .normal := by
  let Inv : Nat → VEnv D → EvmState → Prop :=
    fun remaining V current => ∃ i,
      i + remaining = modulusSize.toNat ∧
      V = ("i", BitVec.ofNat 256 i) :: Vtail ∧
      current = serializePrefix modulusSize i st
  have hcond (i : Nat) (_hi : i ≤ modulusSize.toNat) (current : EvmState) :
      EvalExpr D funs (("i", BitVec.ofNat 256 i) :: Vtail) current
        (yulE% lt(i, modulusSize))
        (.vals [if i < modulusSize.toNat then (1 : U256) else 0] current) := by
    refine Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil
        (Step.var (by simpa [VEnv.get] using hmodulus))) (Step.var rfl)) ?_
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin,
      YulSemantics.EVM.b2w, YulSemantics.EVM.litValue, BitVec.ult]
    simp only [show 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2 ^ 256 by norm_num, Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
    split <;> rfl
  have hpost (i : Nat) (current : EvmState) :
      ExecStmt D funs (("i", BitVec.ofNat 256 i) :: Vtail) current
        (.block incrementI) (("i", BitVec.ofNat 256 (i + 1)) :: Vtail)
        current .normal := by
    let innerFuns : FunEnv D := hoist D incrementI :: funs
    have hadd : EvalExpr D innerFuns (("i", BitVec.ofNat 256 i) :: Vtail)
        current (yulE% add(i, 1))
        (.vals [BitVec.ofNat 256 (i + 1)] current) := by
      have hraw : EvalExpr D innerFuns (("i", BitVec.ofNat 256 i) :: Vtail)
          current (yulE% add(i, 1))
          (.vals [BitVec.ofNat 256 i + 1] current) :=
        Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl
      rw [ofNat_succ] at hraw
      exact hraw
    have hassign := Step.assignVal (D := D) (vars := ["i"]) hadd rfl
    have hset : VEnv.setMany (("i", BitVec.ofNat 256 i) :: Vtail)
        ["i"] [BitVec.ofNat 256 (i + 1)] =
        ("i", BitVec.ofNat 256 (i + 1)) :: Vtail := by rfl
    rw [hset] at hassign
    have hseq := Step.seqCons (D := D) hassign (Step.seqNil (D := D))
    have hblock := Step.block (D := D) hseq
    simpa [innerFuns, incrementI, restore] using hblock
  have hdone : ∀ V current, Inv 0 V current →
      ∃ cv current', EvalExpr D funs V current (yulE% lt(i, modulusSize))
        (.vals [cv] current') ∧ cv = 0 ∧ Inv 0 V current' := by
    intro V current hInv
    obtain ⟨i, hi, rfl, rfl⟩ := hInv
    have hiEq : i = modulusSize.toNat := by omega
    subst i
    exact ⟨0, _, by simpa using hcond modulusSize.toNat (by omega) _, rfl,
      modulusSize.toNat, by omega, rfl, rfl⟩
  have hstep : ∀ remaining V current, Inv (remaining + 1) V current →
      ∃ cv currentCond Vb currentBody ob Vp currentPost,
        EvalExpr D funs V current (yulE% lt(i, modulusSize))
          (.vals [cv] currentCond) ∧ cv ≠ 0 ∧
        ExecStmt D funs V currentCond (.block serializeBody)
          Vb currentBody ob ∧ (ob = .normal ∨ ob = .continue) ∧
        ExecStmt D funs Vb currentBody (.block incrementI)
          Vp currentPost .normal ∧ Inv remaining Vp currentPost := by
    intro remaining V current hInv
    obtain ⟨i, hi, rfl, rfl⟩ := hInv
    have hilt : i < modulusSize.toNat := by omega
    refine ⟨(1 : U256), serializePrefix modulusSize i st,
      ("i", BitVec.ofNat 256 i) :: Vtail,
      serializePrefix modulusSize (i + 1) st, .normal,
      ("i", BitVec.ofNat 256 (i + 1)) :: Vtail,
      serializePrefix modulusSize (i + 1) st, ?_, by decide, ?_, Or.inl rfl,
      ?_, ?_⟩
    · simpa [hilt] using hcond i (by omega) (serializePrefix modulusSize i st)
    · simpa [serializePrefix] using exec_serializeBody Vtail
        (serializePrefix modulusSize i st) modulusSize hmodulus i
    · exact hpost i _
    · exact ⟨i + 1, by omega, rfl, rfl⟩
  obtain ⟨V', current', hloop, hInv⟩ :=
    ExecLoop.countdown (D := D) (funs := funs)
      (cond := yulE% lt(i, modulusSize)) (post := incrementI)
      (body := serializeBody) (Inv := Inv) hdone hstep modulusSize.toNat
      (("i", 0) :: Vtail) st ⟨0, by omega, rfl, rfl⟩
  obtain ⟨i, hi, hV, hstate⟩ := hInv
  have hiEq : i = modulusSize.toNat := by omega
  subst i
  subst V'
  subst current'
  simpa using hloop

end Challenge.Modexp.Reference.Proofs.Yul
