import Challenge.Modexp.Reference.Proofs.Yul.StateModel
import Challenge.YulProof.Interpreter

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Relational contracts for the MODEXP source word path

This module proves the source semantics of the `calldataByte` leaf and the
constant-state arithmetic blocks used by `modexpWord`.  The loop contracts are
stated over the exact executable model from `StateModel`; the arithmetic names
are intentionally aligned with the already-certified bytecode word path in
`Bytecode.WordCorrect`.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul

open YulSemantics
open YulSemantics.EVM
open StateModel
open Challenge.YulProof.Interpreter

private abbrev D := Challenge.YulProof.ClosedEvm.dialect
private abbrev E := Challenge.YulProof.ClosedEvm.exec

private def calldataByteDecl : FDecl D where
  params := ["off"]
  rets := ["b"]
  body := yul% { b := byte(0, calldataload(off)) }

private def modexpWordDecl : FDecl D where
  params := ["bsize", "esize", "modulusSize", "baseOff", "expOff", "modOff"]
  rets := []
  body := yul% {
    let modulus := shr(mul(sub(32, modulusSize), 8), calldataload(modOff))
    if iszero(modulus) { return(0x1800, modulusSize) }

    let base := 0
    for { let i := 0 } lt(i, bsize) { i := add(i, 1) } {
      base := addmod(mulmod(base, 256, modulus),
        calldataByte(add(baseOff, i)), modulus)
    }

    let acc := mod(1, modulus)
    for { let i := 0 } lt(i, esize) { i := add(i, 1) } {
      let w := calldataByte(add(expOff, i))
      for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
        let bit := and(shr(sub(7, j), w), 1)
        let square := mulmod(acc, acc, modulus)
        let product := mulmod(square, base, modulus)
        let mask := sub(0, bit)
        acc := xor(square, and(xor(square, product), mask))
      }
    }

    mstore(0x1800, shl(mul(sub(32, modulusSize), 8), acc))
    return(0x1800, modulusSize)
  }

private theorem lookup_calldataByte :
    lookupFun verifiedFunctions "calldataByte" =
      some (calldataByteDecl, verifiedFunctions) := by
  rfl

private theorem lookup_modexpWord :
    lookupFun verifiedFunctions "modexpWord" =
      some (modexpWordDecl, verifiedFunctions) := by
  rfl

private theorem exec_calldataByteBody (st : EvmState) (off : U256) :
    ExecStmt D verifiedFunctions [("off", off), ("b", 0)] st
      (.block calldataByteDecl.body)
      [("off", off), ("b", calldataByteValue st off)] st .normal := by
  let funs := hoist D calldataByteDecl.body :: verifiedFunctions
  have hload : EvalExpr D funs [("off", off), ("b", 0)] st
      (yulE% calldataload(off))
      (.vals [wordFrom st.env.calldata off.toNat] st) :=
    Step.builtinOk (D := D) (Step.argsCons Step.argsNil (Step.var rfl)) rfl
  have hbyte : EvalExpr D funs [("off", off), ("b", 0)] st
      (yulE% byte(0, calldataload(off)))
      (.vals [calldataByteValue st off] st) := by
    apply Step.builtinOk (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil hload) Step.lit)
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin,
      YulSemantics.EVM.litValue, calldataByteValue]
  exact Step.block (D := D)
    (Step.seqCons (Step.assignVal (by
      simpa [funs, calldataByteDecl] using hbyte) rfl) Step.seqNil)

/-- Direct relational contract for the source `calldataByte` helper. -/
theorem eval_calldataByte {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {arg : Expr Op} (off : U256)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions))
    (harg : EvalExpr D funs V st arg (.vals [off] st1)) :
    EvalExpr D funs V st (.call "calldataByte" [arg])
      (.vals [calldataByteValue st1 off] st1) := by
  refine Step.callOk (D := D)
    (Step.argsCons Step.argsNil harg) hlookup rfl
    (exec_calldataByteBody st1 off) (Or.inl rfl)

private def baseBody : Block Op := yul% {
  base := addmod(mulmod(base, 256, modulus),
    calldataByte(add(baseOff, i)), modulus)
}

private def incrementI : Block Op := yul% { i := add(i, 1) }

private def bitBody : Block Op := yul% {
  let bit := and(shr(sub(7, j), w), 1)
  let square := mulmod(acc, acc, modulus)
  let product := mulmod(square, base, modulus)
  let mask := sub(0, bit)
  acc := xor(square, and(xor(square, product), mask))
}

private def incrementJ : Block Op := yul% { j := add(j, 1) }

private theorem ofNat_succ (i : Nat) :
    BitVec.ofNat 256 i + 1 = BitVec.ofNat 256 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

private def paramsEnv (bsize esize modulusSize baseOff expOff modOff : U256) :
    VEnv D :=
  [("bsize", bsize), ("esize", esize), ("modulusSize", modulusSize),
    ("baseOff", baseOff), ("expOff", expOff), ("modOff", modOff)]

private def baseEnv (bsize esize modulusSize baseOff expOff modOff modulus : U256)
    (i : Nat) (base : U256) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("base", base), ("modulus", modulus)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff

private theorem eval_baseValue {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    EvalExpr D funs
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i base) st
      (yulE% addmod(mulmod(base, 256, modulus),
        calldataByte(add(baseOff, i)), modulus))
      (.vals [baseStep st baseOff modulus i base] st) := by
  have hoff : EvalExpr D funs
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i base) st
      (yulE% add(baseOff, i))
      (.vals [baseOff + BitVec.ofNat 256 i] st) := by
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) rfl
  have hbyte := eval_calldataByte (baseOff + BitVec.ofNat 256 i) hlookup hoff
  have hmul : EvalExpr D funs
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i base) st
      (yulE% mulmod(base, 256, modulus))
      (.vals [mulmodValue base 256 modulus] st) := by
    exact Step.builtinOk
      (Step.argsCons
        (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit)
        (Step.var rfl)) rfl
  unfold baseStep
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) hbyte) hmul)
    rfl

private theorem exec_baseBody {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ExecStmt D funs
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i base) st
      (.block baseBody)
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i
        (baseStep st baseOff modulus i base)) st .normal := by
  have hlookup' : lookupFun (hoist D baseBody :: funs) "calldataByte" =
      some (calldataByteDecl, verifiedFunctions) := by
    simpa [baseBody, hoist, lookupFun] using hlookup
  refine Step.block (D := D)
    (Vb := baseEnv bsize esize modulusSize baseOff expOff modOff modulus i
      (baseStep st baseOff modulus i base)) ?_
  exact Step.seqCons
    (Step.assignVal (eval_baseValue st _ _ _ _ _ _ _ _ i hlookup') rfl)
    Step.seqNil

private theorem exec_incrementI {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat) :
    ExecStmt D funs
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i base) st
      (.block incrementI)
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus (i + 1) base)
      st .normal := by
  have h : ExecStmt D funs
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i base) st
      (.block incrementI)
      ([("i", BitVec.ofNat 256 i + 1), ("base", base), ("modulus", modulus)] ++
        paramsEnv bsize esize modulusSize baseOff expOff modOff) st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ i] at h
  exact h

/-- The source base loop computes the exact Horner prefix and does not change
the EVM state. -/
theorem exec_baseLoop {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus : U256)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ∀ (k i : Nat), i + k = bsize.toNat →
      ExecLoop D funs
        (baseEnv bsize esize modulusSize baseOff expOff modOff modulus i
          (basePrefix st baseOff modulus i)) st
        (yulE% lt(i, bsize)) incrementI baseBody
        (baseEnv bsize esize modulusSize baseOff expOff modOff modulus bsize.toNat
          (basePrefix st baseOff modulus bsize.toNat)) st .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = bsize.toNat := by omega
      subst i
      refine Step.loopDone (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      have hz : D.zero = (0 : U256) := rfl
      rw [hz]
      simp [YulSemantics.EVM.b2w, BitVec.ult, BitVec.toNat_ofNat]
  | succ k ih =>
      intro i hi
      have hilimit : i < bsize.toNat := by omega
      refine Step.loopStep (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_baseBody st bsize esize modulusSize baseOff expOff modOff modulus
          (basePrefix st baseOff modulus i) i hlookup)
        (Or.inl rfl)
        (exec_incrementI st bsize esize modulusSize baseOff expOff modOff modulus
          (baseStep st baseOff modulus i (basePrefix st baseOff modulus i)) i)
        ?_
      · have hz : D.zero = (0 : U256) := rfl
        rw [hz]
        simp only [YulSemantics.EVM.b2w, BitVec.ult, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
        simp [hilimit]
      · simpa [basePrefix] using ih (i + 1) (by omega)

private def expEnv (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat) (acc : U256) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("acc", acc), ("base", base),
    ("modulus", modulus)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff

private def bitEnv (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat) (w : U256) (j : Nat) (acc : U256) : VEnv D :=
  [("j", BitVec.ofNat 256 j), ("w", w)] ++
    expEnv bsize esize modulusSize baseOff expOff modOff modulus base i acc

private theorem exec_bitBody {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat) (w : U256) (j : Nat) (acc : U256) :
    ExecStmt D funs
      (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w j acc) st
      (.block bitBody)
      (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w j
        (bitStep acc base modulus w j)) st .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 100)
  rfl

private theorem exec_incrementJ {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat) (w : U256) (j : Nat) (acc : U256) :
    ExecStmt D funs
      (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w j acc) st
      (.block incrementJ)
      (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w (j + 1) acc)
      st .normal := by
  have h : ExecStmt D funs
      (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w j acc) st
      (.block incrementJ)
      ([("j", BitVec.ofNat 256 j + 1), ("w", w)] ++
        expEnv bsize esize modulusSize baseOff expOff modOff modulus base i acc)
      st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ j] at h
  exact h

/-- The inner source loop performs the eight exact branchless bit steps. -/
theorem exec_bitLoop {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat) (w : U256) (initial : U256) :
    ∀ (k j : Nat), j + k = 8 →
      ExecLoop D funs
        (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w j
          (bitPrefix base modulus w j initial)) st
        (yulE% lt(j, 8)) incrementJ bitBody
        (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w 8
          (bitPrefix base modulus w 8 initial)) st .normal := by
  intro k
  induction k with
  | zero =>
      intro j hj
      have hjeq : j = 8 := by omega
      subst j
      refine Step.loopDone (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl) ?_
      decide
  | succ k ih =>
      intro j hj
      have hj8 : j < 8 := by omega
      refine Step.loopStep (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl) ?_
        (exec_bitBody st bsize esize modulusSize baseOff expOff modOff modulus base i w j
          (bitPrefix base modulus w j initial))
        (Or.inl rfl)
        (exec_incrementJ st bsize esize modulusSize baseOff expOff modOff modulus base i w j
          (bitStep (bitPrefix base modulus w j initial) base modulus w j))
        ?_
      · have hz : D.zero = (0 : U256) := rfl
        rw [hz]
        simp only [YulSemantics.EVM.b2w, BitVec.ult, BitVec.toNat_ofNat,
          YulSemantics.EVM.litValue]
        rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 256)]
        norm_num [hj8]
        decide
      · simpa [bitPrefix] using ih (j + 1) (by omega)

private def exponentBody : Block Op := yul% {
  let w := calldataByte(add(expOff, i))
  for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
    let bit := and(shr(sub(7, j), w), 1)
    let square := mulmod(acc, acc, modulus)
    let product := mulmod(square, base, modulus)
    let mask := sub(0, bit)
    acc := xor(square, and(xor(square, product), mask))
  }
}

private theorem exec_exponentBody {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base : U256)
    (i : Nat) (acc : U256)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ExecStmt D funs
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base i acc) st
      (.block exponentBody)
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base i
        (exponentStep st expOff base modulus i acc)) st .normal := by
  let bodyFuns : FunEnv D := hoist D exponentBody :: funs
  have hlookup' : lookupFun bodyFuns "calldataByte" =
      some (calldataByteDecl, verifiedFunctions) := by
    simpa [bodyFuns, exponentBody, hoist, lookupFun] using hlookup
  have hoff : EvalExpr D bodyFuns
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base i acc) st
      (yulE% add(expOff, i))
      (.vals [expOff + BitVec.ofNat 256 i] st) := by
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) rfl
  have hbyte := eval_calldataByte (expOff + BitVec.ofNat 256 i) hlookup' hoff
  let w := calldataByteValue st (expOff + BitVec.ofNat 256 i)
  have hloop : ExecLoop D
      (hoist D [Stmt.letDecl ["j"] (some (.lit (.number 0)))] :: bodyFuns)
      (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w 0 acc) st
      (yulE% lt(j, 8)) incrementJ bitBody
      (bitEnv bsize esize modulusSize baseOff expOff modOff modulus base i w 8
        (bitPrefix base modulus w 8 acc)) st .normal := by
    exact exec_bitLoop st bsize esize modulusSize baseOff expOff modOff modulus base i w acc
      8 0 (by omega)
  refine Step.block (D := D)
    (Vb := [("w", w)] ++
      expEnv bsize esize modulusSize baseOff expOff modOff modulus base i
        (bitPrefix base modulus w 8 acc)) ?_
  refine Step.seqCons (D := D) (Step.letVal hbyte rfl) ?_
  refine Step.seqCons (D := D) ?_ (Step.seqNil (D := D))
  have hfor := Step.forLoop (D := D)
    (Step.seqCons (D := D) (Step.letVal Step.lit rfl) (Step.seqNil (D := D))) hloop
  convert hfor using 1 <;>
    simp [bodyFuns, exponentBody, incrementJ, bitBody, bitEnv, expEnv,
      paramsEnv, w, restore]

private theorem exec_incrementExpI {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base acc : U256)
    (i : Nat) :
    ExecStmt D funs
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base i acc) st
      (.block incrementI)
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base (i + 1) acc)
      st .normal := by
  have h : ExecStmt D funs
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base i acc) st
      (.block incrementI)
      ([("i", BitVec.ofNat 256 i + 1), ("acc", acc), ("base", base),
        ("modulus", modulus)] ++
        paramsEnv bsize esize modulusSize baseOff expOff modOff) st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ i] at h
  exact h

/-- The outer exponent loop streams every exponent byte through its eight-bit
square-and-multiply loop, without changing EVM state. -/
theorem exec_exponentLoop {funs : FunEnv D} (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff modulus base initial : U256)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ∀ (k i : Nat), i + k = esize.toNat →
      ExecLoop D funs
        (expEnv bsize esize modulusSize baseOff expOff modOff modulus base i
          (exponentPrefix st expOff base modulus i initial)) st
        (yulE% lt(i, esize)) incrementI exponentBody
        (expEnv bsize esize modulusSize baseOff expOff modOff modulus base esize.toNat
          (exponentPrefix st expOff base modulus esize.toNat initial)) st .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = esize.toNat := by omega
      subst i
      refine Step.loopDone (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) rfl) ?_
      have hz : D.zero = (0 : U256) := rfl
      rw [hz]
      simp [YulSemantics.EVM.b2w, BitVec.ult, BitVec.toNat_ofNat]
  | succ k ih =>
      intro i hi
      have hilimit : i < esize.toNat := by omega
      refine Step.loopStep (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) rfl) ?_
        (exec_exponentBody st bsize esize modulusSize baseOff expOff modOff modulus base i
          (exponentPrefix st expOff base modulus i initial) hlookup)
        (Or.inl rfl)
        (exec_incrementExpI st bsize esize modulusSize baseOff expOff modOff modulus base
          (exponentStep st expOff base modulus i
            (exponentPrefix st expOff base modulus i initial)) i)
        ?_
      · have hz : D.zero = (0 : U256) := rfl
        rw [hz]
        simp only [YulSemantics.EVM.b2w, BitVec.ult, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
        simp [hilimit]
      · simpa [exponentPrefix] using ih (i + 1) (by omega)

/-! ### Procedure endpoints -/

private theorem exec_modexpWordBody_zero (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hzero : wordModulus st modulusSize modOff = 0) :
    ExecStmt D verifiedFunctions
      (paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (.block modexpWordDecl.body)
      (paramsEnv bsize esize modulusSize baseOff expOff modOff)
      (zeroModulusReturnedState st modulusSize) .halt := by
  let bodyFuns : FunEnv D := hoist D modexpWordDecl.body :: verifiedFunctions
  let modEnv : VEnv D := [("modulus", wordModulus st modulusSize modOff)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff
  have hmod : EvalExpr D bodyFuns
      (paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (yulE% shr(mul(sub(32, modulusSize), 8), calldataload(modOff)))
      (.vals [wordModulus st modulusSize modOff] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
    rfl
  have hcond : EvalExpr D bodyFuns modEnv st (yulE% iszero(modulus))
      (.vals [(1 : U256)] st) := by
    apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil (Step.var rfl))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un, YulSemantics.EVM.b2w,
      hzero]
  have hret : ExecStmt D bodyFuns modEnv st
      (.block (yul% { return(0x1800, modulusSize) })) modEnv
      (zeroModulusReturnedState st modulusSize) .halt := by
    refine Step.block (D := D) (Vb := modEnv) ?_
    refine Step.seqStop (D := D) (o := .halt) ?_ (by decide)
    refine Step.exprStmtHalt (D := D) ?_
    apply Step.builtinHalt (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit)
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.litValue,
      zeroModulusReturnedState]
  have hif : ExecStmt D bodyFuns modEnv st
      (.cond (yulE% iszero(modulus)) (yul% { return(0x1800, modulusSize) })) modEnv
      (zeroModulusReturnedState st modulusSize) .halt :=
    Step.ifTrue (D := D) hcond (by decide) hret
  refine Step.block (D := D) (Vb := modEnv) ?_
  refine Step.seqCons (D := D) (Step.letVal hmod rfl) ?_
  exact Step.seqStop (D := D) hif (by decide)

/-- The source word procedure's zero-modulus branch halts immediately and
returns the requested slice of the existing output memory. -/
theorem eval_modexpWord_zero {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)}
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hlookup : lookupFun funs "modexpWord" =
      some (modexpWordDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args
      (.vals [bsize, esize, modulusSize, baseOff, expOff, modOff] st1))
    (hzero : wordModulus st1 modulusSize modOff = 0) :
    EvalExpr D funs V st (.call "modexpWord" args)
      (.halt (zeroModulusReturnedState st1 modulusSize)) := by
  exact Step.callHalt (D := D) hargs hlookup rfl
    (exec_modexpWordBody_zero st1 bsize esize modulusSize baseOff expOff modOff hzero)

private theorem exec_modexpWordBody_nonzero (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hnonzero : wordModulus st modulusSize modOff ≠ 0) :
    let modulus := wordModulus st modulusSize modOff
    let base := basePrefix st baseOff modulus bsize.toNat
    let acc := exponentPrefix st expOff base modulus esize.toNat
      (initialAccumulator modulus)
    ExecStmt D verifiedFunctions
      (paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (.block modexpWordDecl.body)
      (paramsEnv bsize esize modulusSize baseOff expOff modOff)
      (wordReturnedState st modulusSize acc) .halt := by
  dsimp only
  let modulus := wordModulus st modulusSize modOff
  let base := basePrefix st baseOff modulus bsize.toNat
  let acc0 := initialAccumulator modulus
  let acc := exponentPrefix st expOff base modulus esize.toNat acc0
  let bodyFuns : FunEnv D := hoist D modexpWordDecl.body :: verifiedFunctions
  let modEnv : VEnv D := [("modulus", modulus)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff
  let baseDone : VEnv D := [("base", base), ("modulus", modulus)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff
  let accDone : VEnv D := [("acc", acc), ("base", base), ("modulus", modulus)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff
  have hmodnz : modulus ≠ 0 := by
    exact hnonzero
  have hmod : EvalExpr D bodyFuns
      (paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (yulE% shr(mul(sub(32, modulusSize), 8), calldataload(modOff)))
      (.vals [modulus] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
    rfl
  have hcond : EvalExpr D bodyFuns modEnv st (yulE% iszero(modulus))
      (.vals [(0 : U256)] st) := by
    apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil (Step.var rfl))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un, YulSemantics.EVM.b2w,
      hmodnz]
    exact hmodnz
  have hif : ExecStmt D bodyFuns modEnv st
      (.cond (yulE% iszero(modulus)) (yul% { return(0x1800, modulusSize) }))
      modEnv st .normal := Step.ifFalse (D := D) hcond rfl
  have hbaseLookup : lookupFun
      (hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] :: bodyFuns)
      "calldataByte" = some (calldataByteDecl, verifiedFunctions) := by
    simpa [bodyFuns, modexpWordDecl, hoist, lookupFun] using lookup_calldataByte
  have hbaseLoop : ExecLoop D
      (hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] :: bodyFuns)
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus 0
        (basePrefix st baseOff modulus 0)) st
      (yulE% lt(i, bsize)) incrementI baseBody
      (baseEnv bsize esize modulusSize baseOff expOff modOff modulus bsize.toNat base)
      st .normal := by
    exact exec_baseLoop st bsize esize modulusSize baseOff expOff modOff modulus
      hbaseLookup bsize.toNat 0 (by omega)
  have hbaseFor : ExecStmt D bodyFuns
      ([("base", (0 : U256)), ("modulus", modulus)] ++
        paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (.forLoop (yul% { let i := 0 }) (yulE% lt(i, bsize)) incrementI baseBody)
      baseDone st .normal := by
    have h := Step.forLoop (D := D)
      (Step.seqCons (D := D) (Step.letVal Step.lit rfl) (Step.seqNil (D := D)))
      hbaseLoop
    convert h using 1 <;>
      simp [baseDone, base, baseEnv, basePrefix, paramsEnv, restore, incrementI,
        baseBody]
  have hacc : EvalExpr D bodyFuns baseDone st (yulE% mod(1, modulus))
      (.vals [acc0] st) := by
    apply Step.builtinOk (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit)
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin, YulSemantics.EVM.litValue, acc0,
      initialAccumulator, hmodnz]
  have hexpLookup : lookupFun
      (hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] :: bodyFuns)
      "calldataByte" = some (calldataByteDecl, verifiedFunctions) := hbaseLookup
  have hexpLoop : ExecLoop D
      (hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] :: bodyFuns)
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base 0
        (exponentPrefix st expOff base modulus 0 acc0)) st
      (yulE% lt(i, esize)) incrementI exponentBody
      (expEnv bsize esize modulusSize baseOff expOff modOff modulus base esize.toNat acc)
      st .normal := by
    exact exec_exponentLoop st bsize esize modulusSize baseOff expOff modOff modulus base acc0
      hexpLookup esize.toNat 0 (by omega)
  have hexpFor : ExecStmt D bodyFuns
      ([("acc", acc0), ("base", base), ("modulus", modulus)] ++
        paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (.forLoop (yul% { let i := 0 }) (yulE% lt(i, esize)) incrementI exponentBody)
      accDone st .normal := by
    have h := Step.forLoop (D := D)
      (Step.seqCons (D := D) (Step.letVal Step.lit rfl) (Step.seqNil (D := D)))
      hexpLoop
    convert h using 1 <;>
      simp [accDone, acc, expEnv, exponentPrefix, paramsEnv, restore, incrementI,
        exponentBody]
  have hmstore : ExecStmt D bodyFuns accDone st
      (.exprStmt
        (yulE% mstore(0x1800, shl(mul(sub(32, modulusSize), 8), acc))))
      accDone (wordStoredState st modulusSize acc) .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 80)
    rfl
  have hreturn : ExecStmt D bodyFuns accDone (wordStoredState st modulusSize acc)
      (.exprStmt (.builtin .ret [.lit (.number 0x1800), .var "modulusSize"])) accDone
      (wordReturnedState st modulusSize acc) .halt := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  refine Step.block (D := D) (Vb := accDone) ?_
  refine Step.seqCons (D := D) (Step.letVal hmod rfl) ?_
  refine Step.seqCons (D := D) hif ?_
  refine Step.seqCons (D := D) (Step.letVal Step.lit rfl) ?_
  refine Step.seqCons (D := D) hbaseFor ?_
  refine Step.seqCons (D := D) (Step.letVal hacc rfl) ?_
  refine Step.seqCons (D := D) hexpFor ?_
  refine Step.seqCons (D := D) hmstore ?_
  exact Step.seqStop (D := D) hreturn (by decide)

/-- Complete relational contract for the nonzero source word path. -/
theorem eval_modexpWord_nonzero {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)}
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hlookup : lookupFun funs "modexpWord" =
      some (modexpWordDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args
      (.vals [bsize, esize, modulusSize, baseOff, expOff, modOff] st1))
    (hnonzero : wordModulus st1 modulusSize modOff ≠ 0) :
    let modulus := wordModulus st1 modulusSize modOff
    let base := basePrefix st1 baseOff modulus bsize.toNat
    let acc := exponentPrefix st1 expOff base modulus esize.toNat
      (initialAccumulator modulus)
    EvalExpr D funs V st (.call "modexpWord" args)
      (.halt (wordReturnedState st1 modulusSize acc)) := by
  dsimp only
  exact Step.callHalt (D := D) hargs hlookup rfl
    (exec_modexpWordBody_nonzero st1 bsize esize modulusSize baseOff expOff modOff
      hnonzero)

end Challenge.Modexp.Reference.Proofs.Yul
