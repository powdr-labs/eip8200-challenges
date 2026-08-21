import Challenge.Modexp.Reference.Proofs.Yul.Procedures
import Challenge.Modexp.Reference.Proofs.Yul.BigArithmetic
import Challenge.Modexp.Reference.Proofs.Yul.BigDriver
import Challenge.Modexp.Reference.Proofs.Yul.BigMul
import Challenge.YulProof.Interpreter

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Exact source-Yul execution of the MODEXP big-path setup

This module composes the independently proved source contracts for clearing
limb arrays, loading the modulus, and scanning it for zero.  In particular,
the zero-modulus endpoint executes the readable `modexpBig` AST directly and
halts with the source return slice; it does not pass through compiled EVM.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigPath

open YulSemantics
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open Challenge.YulProof.Interpreter
open Challenge.Modexp.Reference.Proofs.Yul
open Challenge.Modexp.Reference.Proofs.Yul.Procedures

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

private theorem dialect_zero : D.zero = (0 : U256) := rfl

private def calldataByteDecl : FDecl D where
  params := ["off"]
  rets := ["b"]
  body := yul% { b := byte(0, calldataload(off)) }

private theorem exec_calldataByteBody (st : EvmState) (off : U256) :
    ExecStmt D verifiedFunctions [("off", off), ("b", 0)] st
      (.block calldataByteDecl.body)
      [("off", off), ("b", StateModel.calldataByteValue st off)] st .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
  rfl

private theorem eval_calldataByte {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {arg : Expr Op} (off : U256)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions))
    (harg : EvalExpr D funs V st arg (.vals [off] st1)) :
    EvalExpr D funs V st (.call "calldataByte" [arg])
      (.vals [StateModel.calldataByteValue st1 off] st1) := by
  exact Step.callOk (D := D) (Step.argsCons Step.argsNil harg) hlookup rfl
    (exec_calldataByteBody st1 off) (Or.inl rfl)

private def modexpBigDecl : FDecl D where
  params := ["bsize", "esize", "modulusSize", "baseOff", "expOff", "modOff"]
  rets := []
  body := yul% {
    let n := div(add(modulusSize, 31), 32)
    clearLimbs(0x0000, n)
    clearLimbs(0x0400, n)
    clearLimbs(0x0800, n)
    clearLimbs(0x1800, n)
    loadBigEndian(modOff, modulusSize, 0x0000)

    let modulusOr := 0
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      modulusOr := or(modulusOr, mload(mul(i, 32)))
    }
    if iszero(modulusOr) { return(0x1800, modulusSize) }

    clearLimbs(0x0c00, n)
    mstore(0x0c00, 1)
    for { let i := 0 } lt(i, bsize) { i := add(i, 1) } {
      let w := calldataByte(add(baseOff, i))
      for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
        addMaskedMod(0x0400, 0x0400, 1, 0x0000, n)
        addMaskedMod(0x0400, 0x0c00,
          and(shr(sub(7, j), w), 1), 0x0000, n)
      }
    }

    addMaskedMod(0x0800, 0x0c00, 1, 0x0000, n)

    for { let i := 0 } lt(i, esize) { i := add(i, 1) } {
      let w := calldataByte(add(expOff, i))
      for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
        let bit := and(shr(sub(7, j), w), 1)

        mulModBig(0x0800, 0x0800, 0x0c00, 0x0000, n)
        copyLimbs(0x0800, 0x0c00, n)
        mulModBig(0x0800, 0x0400, 0x0c00, 0x0000, n)

        let mask := sub(0, bit)
        for { let k := 0 } lt(k, n) { k := add(k, 1) } {
          let off := mul(k, 32)
          let square := mload(add(0x0800, off))
          let product := mload(add(0x0c00, off))
          mstore(add(0x0800, off),
            xor(square, and(xor(square, product), mask)))
        }
      }
    }

    for { let i := 0 } lt(i, modulusSize) { i := add(i, 1) } {
      let reverse := sub(sub(modulusSize, 1), i)
      let limb := div(reverse, 32)
      let shift := mul(mod(reverse, 32), 8)
      mstore8(add(0x1800, i),
        and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff))
    }
    return(0x1800, modulusSize)
  }

private theorem lookup_modexpBig :
    lookupFun verifiedFunctions "modexpBig" =
      some (modexpBigDecl, verifiedFunctions) := by
  rfl

def limbCount (modulusSize : U256) : U256 :=
  (modulusSize + 31) / 32

private def paramsEnv (bsize esize modulusSize baseOff expOff modOff : U256) :
    VEnv D :=
  [("bsize", bsize), ("esize", esize), ("modulusSize", modulusSize),
    ("baseOff", baseOff), ("expOff", expOff), ("modOff", modOff)]

def clearedModulusState (st : EvmState) (modulusSize : U256) : EvmState :=
  clearWordsState st 0x0000 (limbCount modulusSize).toNat

def clearedBaseState (st : EvmState) (modulusSize : U256) : EvmState :=
  clearWordsState (clearedModulusState st modulusSize) 0x0400
    (limbCount modulusSize).toNat

def clearedAccumulatorState (st : EvmState) (modulusSize : U256) : EvmState :=
  clearWordsState (clearedBaseState st modulusSize) 0x0800
    (limbCount modulusSize).toNat

def clearedOutputState (st : EvmState) (modulusSize : U256) : EvmState :=
  clearWordsState (clearedAccumulatorState st modulusSize) 0x1800
    (limbCount modulusSize).toNat

def loadedModulusState (st : EvmState) (modulusSize modOff : U256) : EvmState :=
  loadBigEndianPrefix (clearedOutputState st modulusSize) modOff modulusSize
    0x0000 modulusSize.toNat

def scannedModulusState (st : EvmState) (modulusSize modOff : U256) : EvmState :=
  modulusScanPrefix (limbCount modulusSize).toNat
    (loadedModulusState st modulusSize modOff)

def modulusOrValue (st : EvmState) (modulusSize modOff : U256) : U256 :=
  modulusOrPrefix (limbCount modulusSize).toNat
    (loadedModulusState st modulusSize modOff)

def zeroModulusReturnedState (st : EvmState) (modulusSize modOff : U256) :
    EvmState :=
  let scanned := scannedModulusState st modulusSize modOff
  { touchMemory scanned 0x1800 modulusSize.toNat with
    halted := some (.ret, readBytes scanned.memory 0x1800 modulusSize.toNat) }

private theorem exec_modexpBigBody_zero (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hzero : modulusOrValue st modulusSize modOff = 0) :
    ExecStmt D verifiedFunctions
      (paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (.block modexpBigDecl.body)
      (paramsEnv bsize esize modulusSize baseOff expOff modOff)
      (zeroModulusReturnedState st modulusSize modOff) .halt := by
  let n := limbCount modulusSize
  let Vparams := paramsEnv bsize esize modulusSize baseOff expOff modOff
  let Vn : VEnv D := ("n", n) :: Vparams
  let Vscan : VEnv D := ("modulusOr", modulusOrValue st modulusSize modOff) :: Vn
  let s0 := clearedModulusState st modulusSize
  let s1 := clearedBaseState st modulusSize
  let s2 := clearedAccumulatorState st modulusSize
  let s3 := clearedOutputState st modulusSize
  let s4 := loadedModulusState st modulusSize modOff
  let s5 := scannedModulusState st modulusSize modOff
  let bodyFuns : FunEnv D := hoist D modexpBigDecl.body :: verifiedFunctions
  let scanFuns : FunEnv D := [] :: bodyFuns
  have hn : EvalExpr D bodyFuns Vparams st
      (yulE% div(add(modulusSize, 31), 32)) (.vals [n] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 40)
    rfl
  have hclear0 : EvalExpr D bodyFuns Vn st (yulE% clearLimbs(0x0000, n))
      (.vals [] s0) := by
    simpa [bodyFuns, Vn, s0, clearedModulusState, n, limbCount, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := st)
        (ptr := (0x0000 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hclear1 : EvalExpr D bodyFuns Vn s0 (yulE% clearLimbs(0x0400, n))
      (.vals [] s1) := by
    simpa [bodyFuns, Vn, s0, s1, clearedBaseState, n, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := s0)
        (ptr := (0x0400 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hclear2 : EvalExpr D bodyFuns Vn s1 (yulE% clearLimbs(0x0800, n))
      (.vals [] s2) := by
    simpa [bodyFuns, Vn, s1, s2, clearedAccumulatorState, n, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := s1)
        (ptr := (0x0800 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hclear3 : EvalExpr D bodyFuns Vn s2 (yulE% clearLimbs(0x1800, n))
      (.vals [] s3) := by
    simpa [bodyFuns, Vn, s2, s3, clearedOutputState, n, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := s2)
        (ptr := (0x1800 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hload : EvalExpr D bodyFuns Vn s3
      (yulE% loadBigEndian(modOff, modulusSize, 0x0000)) (.vals [] s4) := by
    simpa [bodyFuns, Vn, s3, s4, loadedModulusState, mkCall, parse] using
      (eval_loadBigEndian (funs := bodyFuns) (V := Vn) (st := s3)
        modOff modulusSize (0x0000 : U256) (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 30)
          rfl))
  have hscan := exec_modulusScanLoop (funs := scanFuns) Vparams s4 n
  have hcond : EvalExpr D bodyFuns Vscan s5 (yulE% iszero(modulusOr))
      (.vals [(1 : U256)] s5) := by
    apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil (Step.var rfl))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un, YulSemantics.EVM.b2w,
      Vscan, hzero]
  have hret : ExecStmt D bodyFuns Vscan s5
      (.block (yul% { return(0x1800, modulusSize) })) Vscan
      (zeroModulusReturnedState st modulusSize modOff) .halt := by
    refine Step.block (D := D) (Vb := Vscan) ?_
    refine Step.seqStop (D := D) (o := .halt) ?_ (by decide)
    refine Step.exprStmtHalt (D := D) ?_
    apply Step.builtinHalt (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit)
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.litValue,
      zeroModulusReturnedState, s5]
  have hif : ExecStmt D bodyFuns Vscan s5
      (.cond (yulE% iszero(modulusOr))
        (yul% { return(0x1800, modulusSize) })) Vscan
      (zeroModulusReturnedState st modulusSize modOff) .halt :=
    Step.ifTrue (D := D) hcond (by decide) hret
  simp only [modexpBigDecl]
  refine Step.block (D := D) (Vb := Vscan) ?_
  refine Step.seqCons (D := D) (Step.letVal hn rfl) ?_
  refine Step.seqCons (Step.exprStmt hclear0) ?_
  refine Step.seqCons (Step.exprStmt hclear1) ?_
  refine Step.seqCons (Step.exprStmt hclear2) ?_
  refine Step.seqCons (Step.exprStmt hclear3) ?_
  refine Step.seqCons (Step.exprStmt hload) ?_
  refine Step.seqCons (Step.letVal Step.lit rfl) ?_
  refine Step.seqCons (D := D) (V1 := Vscan) (st1 := s5) ?_ ?_
  · refine Step.forLoop (D := D)
      (Vinit := Challenge.Modexp.Reference.Proofs.Yul.scanEnv n Vparams 0 0)
      (stinit := s4)
      (Vend := Challenge.Modexp.Reference.Proofs.Yul.scanEnv n Vparams n.toNat
        (modulusOrValue st modulusSize modOff)) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa only [scanFuns, bodyFuns, modexpBigDecl, hoist, List.filterMap,
        Challenge.Modexp.Reference.Proofs.Yul.incrementI,
        Challenge.Modexp.Reference.Proofs.Yul.modulusScanBody,
        Vscan, Vn, s4, s5, scannedModulusState, modulusOrValue, n] using hscan
  exact Step.seqStop (D := D) hif (by decide)

/-- The source `modexpBig` helper halts at the zero-modulus guard after the
exact four clears, modulus load, and modulus scan represented above. -/
theorem eval_modexpBig_zero {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)}
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hlookup : lookupFun funs "modexpBig" =
      some (modexpBigDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args
      (.vals [bsize, esize, modulusSize, baseOff, expOff, modOff] st1))
    (hzero : modulusOrValue st1 modulusSize modOff = 0) :
    EvalExpr D funs V st (.call "modexpBig" args)
      (.halt (zeroModulusReturnedState st1 modulusSize modOff)) := by
  exact Step.callHalt (D := D) hargs hlookup rfl
    (exec_modexpBigBody_zero st1 bsize esize modulusSize baseOff expOff modOff hzero)

/-- Lookup-specialized zero-modulus contract for calls from the verified
MODEXP program. -/
theorem eval_modexpBig_zero_verified {V : VEnv D} {st st1 : EvmState}
    {args : List (Expr Op)}
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hargs : EvalArgs D verifiedFunctions V st args
      (.vals [bsize, esize, modulusSize, baseOff, expOff, modOff] st1))
    (hzero : modulusOrValue st1 modulusSize modOff = 0) :
    EvalExpr D verifiedFunctions V st (.call "modexpBig" args)
      (.halt (zeroModulusReturnedState st1 modulusSize modOff)) := by
  exact eval_modexpBig_zero bsize esize modulusSize baseOff expOff modOff
    lookup_modexpBig hargs hzero

/-! ## Nonzero prelude and base conversion -/

def scratchClearedState (st : EvmState) (modulusSize modOff : U256) : EvmState :=
  clearWordsState (scannedModulusState st modulusSize modOff) 0x0c00
    (limbCount modulusSize).toNat

def scratchOneState (st : EvmState) (modulusSize modOff : U256) : EvmState :=
  storeWordAt (scratchClearedState st modulusSize modOff) 0x0c00 1

def baseBit (word : U256) (j : Nat) : U256 :=
  (word >>> (7 - BitVec.ofNat 256 j).toNat) &&& 1

def baseBitStep (n word : U256) (j : Nat) (current : EvmState) : EvmState :=
  let doubled := BigArithmetic.addMaskedModState current
    0x0400 0x0400 1 0x0000 n.toNat
  BigArithmetic.addMaskedModState doubled
    0x0400 0x0c00 (baseBit word j) 0x0000 n.toNat

def baseBitPrefix (n word : U256) : Nat → EvmState → EvmState
  | 0, current => current
  | j + 1, current => baseBitStep n word j (baseBitPrefix n word j current)

def baseByteStep (baseOff n : U256) (i : Nat) (current : EvmState) : EvmState :=
  let word := StateModel.calldataByteValue current
    (baseOff + BitVec.ofNat 256 i)
  baseBitPrefix n word 8 current

def baseBytePrefix (baseOff n : U256) : Nat → EvmState → EvmState
  | 0, current => current
  | i + 1, current => baseByteStep baseOff n i
      (baseBytePrefix baseOff n i current)

def convertedBaseState (st : EvmState) (bsize modulusSize baseOff modOff : U256) :
    EvmState :=
  baseBytePrefix baseOff (limbCount modulusSize) bsize.toNat
    (scratchOneState st modulusSize modOff)

def initializedAccumulatorState (st : EvmState)
    (bsize modulusSize baseOff modOff : U256) : EvmState :=
  BigArithmetic.addMaskedModState
    (convertedBaseState st bsize modulusSize baseOff modOff)
    0x0800 0x0c00 1 0x0000 (limbCount modulusSize).toNat

private def incrementI : Block Op := yul% { i := add(i, 1) }
private def incrementJ : Block Op := yul% { j := add(j, 1) }

private def baseInnerBody : Block Op := yul% {
  addMaskedMod(0x0400, 0x0400, 1, 0x0000, n)
  addMaskedMod(0x0400, 0x0c00,
    and(shr(sub(7, j), w), 1), 0x0000, n)
}

private def baseOuterBody : Block Op := yul% {
  let w := calldataByte(add(baseOff, i))
  for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
    addMaskedMod(0x0400, 0x0400, 1, 0x0000, n)
    addMaskedMod(0x0400, 0x0c00,
      and(shr(sub(7, j), w), 1), 0x0000, n)
  }
}

private def baseOuterEnv (bsize esize modulusSize baseOff expOff modOff n
    modulusOr : U256) (i : Nat) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("modulusOr", modulusOr), ("n", n)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff

private def baseInnerEnv (bsize esize modulusSize baseOff expOff modOff n
    modulusOr word : U256) (i j : Nat) : VEnv D :=
  [("j", BitVec.ofNat 256 j), ("w", word), ("i", BitVec.ofNat 256 i),
    ("modulusOr", modulusOr), ("n", n)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff

private theorem ofNat_succ (i : Nat) :
    BitVec.ofNat 256 i + 1 = BitVec.ofNat 256 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

private theorem exec_incrementJ {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word : U256)
    (i j : Nat) :
    ExecStmt D funs
      (baseInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i j) current (.block incrementJ)
      (baseInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i (j + 1)) current .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
  simp only [incrementJ, baseInnerEnv, paramsEnv]
  rw [← ofNat_succ]
  rfl

private theorem exec_incrementI {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr : U256)
    (i : Nat) :
    ExecStmt D funs
      (baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
      current (.block incrementI)
      (baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        (i + 1)) current .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
  simp only [incrementI, baseOuterEnv, paramsEnv]
  rw [← ofNat_succ]
  rfl

private theorem exec_baseInnerBody {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word : U256)
    (i j : Nat)
    (hlookup : lookupFun (hoist D baseInnerBody :: funs) "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod") :
    ExecStmt D funs
      (baseInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i j) current (.block baseInnerBody)
      (baseInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i j) (baseBitStep n word j current) .normal := by
  let V := baseInnerEnv bsize esize modulusSize baseOff expOff modOff n
    modulusOr word i j
  let doubled := BigArithmetic.addMaskedModState current
    0x0400 0x0400 1 0x0000 n.toNat
  let bit := baseBit word j
  let bodyFuns : FunEnv D := hoist D baseInnerBody :: funs
  have hargs1 : EvalArgs D bodyFuns V current
      [yulE% 0x0400, yulE% 0x0400, yulE% 1, yulE% 0x0000, yulE% n]
      (.vals [0x0400, 0x0400, 1, 0x0000, n] current) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 60)
    rfl
  have hadd1 : EvalExpr D bodyFuns V current
      (yulE% addMaskedMod(0x0400, 0x0400, 1, 0x0000, n))
      (.vals [] doubled) := by
    simpa [bodyFuns, doubled, mkCall, parse] using
      (BigArithmetic.eval_addMaskedMod (funs := bodyFuns) (V := V)
        (st := current) (0x0400 : U256) 0x0400 1 0x0000 n
        (by rw [hlookup]; rfl) hargs1)
  have hargs2 : EvalArgs D bodyFuns V doubled
      [yulE% 0x0400, yulE% 0x0c00,
        yulE% and(shr(sub(7, j), w), 1), yulE% 0x0000, yulE% n]
      (.vals [0x0400, 0x0c00, bit, 0x0000, n] doubled) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 100)
    rfl
  have hadd2 : EvalExpr D bodyFuns V doubled
      (yulE% addMaskedMod(0x0400, 0x0c00,
        and(shr(sub(7, j), w), 1), 0x0000, n))
      (.vals [] (baseBitStep n word j current)) := by
    simpa [bodyFuns, doubled, bit, baseBitStep, baseBit, mkCall, parse] using
      (BigArithmetic.eval_addMaskedMod (funs := bodyFuns) (V := V)
        (st := doubled) (0x0400 : U256) 0x0c00 bit 0x0000 n
        (by rw [hlookup]; rfl) hargs2)
  refine Step.block (D := D) (Vb := V) ?_
  refine Step.seqCons (Step.exprStmt hadd1) ?_
  refine Step.seqCons (Step.exprStmt hadd2) Step.seqNil

private theorem exec_baseInnerLoop {funs : FunEnv D} (initial : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word : U256)
    (i : Nat)
    (hlookup : lookupFun funs "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod") :
    ∀ (k j : Nat), j + k = 8 →
      ExecLoop D funs
        (baseInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          word i j) (baseBitPrefix n word j initial)
        (yulE% lt(j, 8)) incrementJ baseInnerBody
        (baseInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          word i 8) (baseBitPrefix n word 8 initial) .normal := by
  intro k
  induction k with
  | zero =>
      intro j hj
      have : j = 8 := by omega
      subst j
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl)
        ?_
      norm_num [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal, dialect_zero,
        YulSemantics.EVM.b2w, BitVec.ult, YulSemantics.EVM.litValue]
  | succ k ih =>
      intro j hj
      have hj8 : j < 8 := by omega
      have hlookup' : lookupFun (hoist D baseInnerBody :: funs) "addMaskedMod" =
          lookupFun verifiedFunctions "addMaskedMod" := by
        simpa [baseInnerBody, hoist, lookupFun] using hlookup
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl)
        ?_
        (exec_baseInnerBody (baseBitPrefix n word j initial)
          bsize esize modulusSize baseOff expOff modOff n modulusOr word i j
          hlookup')
        (Or.inl rfl)
        (exec_incrementJ (baseBitPrefix n word (j + 1) initial)
          bsize esize modulusSize baseOff expOff modOff n modulusOr word i j)
        ?_
      · rw [dialect_zero]
        simp [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.b2w, BitVec.ult,
          YulSemantics.EVM.litValue]
        have hjM : j <
            115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
          by omega
        rw [Nat.mod_eq_of_lt hjM]
        exact hj8
      · simpa [baseBitPrefix] using ih (j + 1) (by omega)

private theorem exec_baseOuterBody {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr : U256)
    (i : Nat)
    (hadd : lookupFun funs "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod")
    (hbyte : lookupFun (hoist D baseOuterBody :: funs) "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ExecStmt D funs
      (baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
      current (.block baseOuterBody)
      (baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
      (baseByteStep baseOff n i current) .normal := by
  let V := baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i
  let off := baseOff + BitVec.ofNat 256 i
  let word := StateModel.calldataByteValue current off
  let bodyFuns : FunEnv D := hoist D baseOuterBody :: funs
  let loopFuns : FunEnv D := [] :: bodyFuns
  have hoff : EvalExpr D bodyFuns V current (yulE% add(baseOff, i))
      (.vals [off] current) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  have hw : EvalExpr D bodyFuns V current
      (yulE% calldataByte(add(baseOff, i))) (.vals [word] current) := by
    simpa [bodyFuns, word, off, mkCall, parse] using
      (eval_calldataByte off hbyte hoff)
  have hadd' : lookupFun loopFuns "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod" := by
    simpa [loopFuns, bodyFuns, baseOuterBody, hoist, lookupFun] using hadd
  refine Step.block (D := D)
    (Vb := ("w", word) ::
      baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i) ?_
  refine Step.seqCons (Step.letVal hw rfl) ?_
  refine Step.seqCons ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := baseInnerEnv bsize esize modulusSize baseOff expOff modOff n
      modulusOr word i 0) (stinit := current)
    (Vend := baseInnerEnv bsize esize modulusSize baseOff expOff modOff n
      modulusOr word i 8) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · simpa [loopFuns, bodyFuns, baseOuterBody, baseInnerBody, incrementJ,
      baseByteStep, baseBitPrefix, word, off, hoist] using
      exec_baseInnerLoop (funs := loopFuns) current bsize esize modulusSize
        baseOff expOff modOff n modulusOr word i hadd' 8 0 (by omega)

private theorem exec_baseOuterLoop {funs : FunEnv D} (initial : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr : U256)
    (hadd : lookupFun funs "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod")
    (hbyte : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ∀ (k i : Nat), i + k = bsize.toNat →
      ExecLoop D funs
        (baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
        (baseBytePrefix baseOff n i initial)
        (yulE% lt(i, bsize)) incrementI baseOuterBody
        (baseOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          bsize.toNat)
        (baseBytePrefix baseOff n bsize.toNat initial) .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have : i = bsize.toNat := by omega
      subst i
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal, dialect_zero,
        YulSemantics.EVM.b2w, BitVec.ult]
  | succ k ih =>
      intro i hi
      have hib : i < bsize.toNat := by omega
      have hbyte' : lookupFun (hoist D baseOuterBody :: funs) "calldataByte" =
          some (calldataByteDecl, verifiedFunctions) := by
        simpa [baseOuterBody, hoist, lookupFun] using hbyte
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_baseOuterBody (baseBytePrefix baseOff n i initial)
          bsize esize modulusSize baseOff expOff modOff n modulusOr i hadd hbyte')
        (Or.inl rfl)
        (exec_incrementI (baseBytePrefix baseOff n (i + 1) initial)
          bsize esize modulusSize baseOff expOff modOff n modulusOr i) ?_
      · rw [dialect_zero]
        simp [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.b2w, BitVec.ult]
        rw [Nat.mod_eq_of_lt (hib.trans bsize.isLt)]
        exact hib
      · simpa [baseBytePrefix] using ih (i + 1) (by omega)

/-- Exact source execution of the nonzero big-path prelude: scratch setup,
base conversion, and accumulator initialization. -/
theorem exec_nonzeroPrelude (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (_hnonzero : modulusOrValue st modulusSize modOff ≠ 0) :
    let n := limbCount modulusSize
    let V := ("modulusOr", modulusOrValue st modulusSize modOff) ::
      ("n", n) :: paramsEnv bsize esize modulusSize baseOff expOff modOff
    ExecStmts D ([] :: verifiedFunctions) V (scannedModulusState st modulusSize modOff)
      (yul% {
        clearLimbs(0x0c00, n)
        mstore(0x0c00, 1)
        for { let i := 0 } lt(i, bsize) { i := add(i, 1) } {
          let w := calldataByte(add(baseOff, i))
          for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
            addMaskedMod(0x0400, 0x0400, 1, 0x0000, n)
            addMaskedMod(0x0400, 0x0c00,
              and(shr(sub(7, j), w), 1), 0x0000, n)
          }
        }
        addMaskedMod(0x0800, 0x0c00, 1, 0x0000, n)
      }) V (initializedAccumulatorState st bsize modulusSize baseOff modOff)
      .normal := by
  dsimp only
  let n := limbCount modulusSize
  let modulusOr := modulusOrValue st modulusSize modOff
  let V := ("modulusOr", modulusOr) :: ("n", n) ::
    paramsEnv bsize esize modulusSize baseOff expOff modOff
  let scanned := scannedModulusState st modulusSize modOff
  let cleared := scratchClearedState st modulusSize modOff
  let one := scratchOneState st modulusSize modOff
  let converted := convertedBaseState st bsize modulusSize baseOff modOff
  let initialized := initializedAccumulatorState st bsize modulusSize baseOff modOff
  let bodyFuns : FunEnv D := [] :: verifiedFunctions
  let loopFuns : FunEnv D := [] :: bodyFuns
  have hclearArgs : EvalArgs D bodyFuns V scanned
      [yulE% 0x0c00, yulE% n] (.vals [0x0c00, n] scanned) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  have hclear : EvalExpr D bodyFuns V scanned
      (yulE% clearLimbs(0x0c00, n)) (.vals [] cleared) := by
    simpa [cleared, scratchClearedState, scanned, n, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := V) (st := scanned)
        (0x0c00 : U256) n (by rfl) hclearArgs)
  have hone : EvalExpr D bodyFuns V cleared (yulE% mstore(0x0c00, 1))
      (.vals [] one) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  have hadd : lookupFun loopFuns "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod" := by rfl
  have hbyte : lookupFun loopFuns "calldataByte" =
      some (calldataByteDecl, verifiedFunctions) := by rfl
  have hbase := exec_baseOuterLoop (funs := loopFuns) one bsize esize
    modulusSize baseOff expOff modOff n modulusOr hadd hbyte bsize.toNat 0 (by omega)
  have haccArgs : EvalArgs D bodyFuns V converted
      [yulE% 0x0800, yulE% 0x0c00, yulE% 1, yulE% 0x0000, yulE% n]
      (.vals [0x0800, 0x0c00, 1, 0x0000, n] converted) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 60)
    rfl
  have hacc : EvalExpr D bodyFuns V converted
      (yulE% addMaskedMod(0x0800, 0x0c00, 1, 0x0000, n))
      (.vals [] initialized) := by
    simpa [initialized, initializedAccumulatorState, converted, n, mkCall, parse]
      using (BigArithmetic.eval_addMaskedMod (funs := bodyFuns) (V := V)
        (st := converted) (0x0800 : U256) 0x0c00 1 0x0000 n (by rfl) haccArgs)
  refine Step.seqCons (Step.exprStmt hclear) ?_
  refine Step.seqCons (Step.exprStmt hone) ?_
  refine Step.seqCons (V1 := V) (st1 := converted) ?_ ?_
  · refine Step.forLoop (D := D)
      (Vinit := baseOuterEnv bsize esize modulusSize baseOff expOff modOff n
        modulusOr 0) (stinit := one)
      (Vend := baseOuterEnv bsize esize modulusSize baseOff expOff modOff n
        modulusOr bsize.toNat) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa [loopFuns, baseOuterEnv, baseOuterBody, incrementI, converted,
        convertedBaseState, baseBytePrefix, n, one, hoist] using hbase
  exact Step.seqCons (Step.exprStmt hacc) Step.seqNil

/-! ## Big square-and-multiply state model -/

def selectLimbStep (mask : U256) (k : Nat) (current : EvmState) : EvmState :=
  let off := BitVec.ofNat 256 k * 32
  let squareAt : U256 := 0x0800 + off
  let productAt : U256 := 0x0c00 + off
  let square := loadWord current.memory squareAt.toNat
  let afterSquare := touchMemory current squareAt.toNat 32
  let product := loadWord afterSquare.memory productAt.toNat
  let afterProduct := touchMemory afterSquare productAt.toNat 32
  storeWordAt afterProduct squareAt
    (square ^^^ ((square ^^^ product) &&& mask))

def selectLimbPrefix (mask : U256) : Nat → EvmState → EvmState
  | 0, current => current
  | k + 1, current => selectLimbStep mask k (selectLimbPrefix mask k current)

def exponentBitStep (n word : U256) (j : Nat) (current : EvmState) : EvmState :=
  let bit := baseBit word j
  let squared := BigMul.mulModBigState current 0x0800 0x0800 0x0c00 0x0000 n
  let copied := copyWordsState squared 0x0800 0x0c00 n.toNat
  let product := BigMul.mulModBigState copied 0x0800 0x0400 0x0c00 0x0000 n
  selectLimbPrefix (0 - bit) n.toNat product

def exponentBitPrefix (n word : U256) : Nat → EvmState → EvmState
  | 0, current => current
  | j + 1, current => exponentBitStep n word j
      (exponentBitPrefix n word j current)

def exponentByteStep (expOff n : U256) (i : Nat)
    (current : EvmState) : EvmState :=
  let word := StateModel.calldataByteValue current
    (expOff + BitVec.ofNat 256 i)
  exponentBitPrefix n word 8 current

def exponentBytePrefix (expOff n : U256) : Nat → EvmState → EvmState
  | 0, current => current
  | i + 1, current => exponentByteStep expOff n i
      (exponentBytePrefix expOff n i current)

def exponentiatedState (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256) : EvmState :=
  exponentBytePrefix expOff (limbCount modulusSize) esize.toNat
    (initializedAccumulatorState st bsize modulusSize baseOff modOff)

private def expOuterEnv (bsize esize modulusSize baseOff expOff modOff n
    modulusOr : U256) (i : Nat) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("modulusOr", modulusOr), ("n", n)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff

private def expInnerEnv (bsize esize modulusSize baseOff expOff modOff n
    modulusOr word : U256) (i j : Nat) : VEnv D :=
  [("j", BitVec.ofNat 256 j), ("w", word), ("i", BitVec.ofNat 256 i),
    ("modulusOr", modulusOr), ("n", n)] ++
    paramsEnv bsize esize modulusSize baseOff expOff modOff

private def expBitEnv (bsize esize modulusSize baseOff expOff modOff n
    modulusOr word bit : U256) (i j : Nat) : VEnv D :=
  [("bit", bit)] ++ expInnerEnv bsize esize modulusSize baseOff expOff modOff
    n modulusOr word i j

private def expMaskEnv (bsize esize modulusSize baseOff expOff modOff n
    modulusOr word bit mask : U256) (i j : Nat) : VEnv D :=
  [("mask", mask), ("bit", bit)] ++
    expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word i j

private def expSelectEnv (bsize esize modulusSize baseOff expOff modOff n
    modulusOr word bit mask : U256) (i j k : Nat) : VEnv D :=
  [("k", BitVec.ofNat 256 k), ("mask", mask), ("bit", bit)] ++
    expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word i j

private def expSelectBody : Block Op := yul% {
  let off := mul(k, 32)
  let square := mload(add(0x0800, off))
  let product := mload(add(0x0c00, off))
  mstore(add(0x0800, off),
    xor(square, and(xor(square, product), mask)))
}

private def expBitBody : Block Op := yul% {
  let bit := and(shr(sub(7, j), w), 1)
  mulModBig(0x0800, 0x0800, 0x0c00, 0x0000, n)
  copyLimbs(0x0800, 0x0c00, n)
  mulModBig(0x0800, 0x0400, 0x0c00, 0x0000, n)
  let mask := sub(0, bit)
  for { let k := 0 } lt(k, n) { k := add(k, 1) } {
    let off := mul(k, 32)
    let square := mload(add(0x0800, off))
    let product := mload(add(0x0c00, off))
    mstore(add(0x0800, off),
      xor(square, and(xor(square, product), mask)))
  }
}

private def expOuterBody : Block Op := yul% {
  let w := calldataByte(add(expOff, i))
  for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
    let bit := and(shr(sub(7, j), w), 1)
    mulModBig(0x0800, 0x0800, 0x0c00, 0x0000, n)
    copyLimbs(0x0800, 0x0c00, n)
    mulModBig(0x0800, 0x0400, 0x0c00, 0x0000, n)
    let mask := sub(0, bit)
    for { let k := 0 } lt(k, n) { k := add(k, 1) } {
      let off := mul(k, 32)
      let square := mload(add(0x0800, off))
      let product := mload(add(0x0c00, off))
      mstore(add(0x0800, off),
        xor(square, and(xor(square, product), mask)))
    }
  }
}

private theorem exec_expIncrementK {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word bit mask : U256)
    (i j k : Nat) :
    ExecStmt D funs
      (expSelectEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word bit mask i j k) current (.block (yul% { k := add(k, 1) }))
      (expSelectEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word bit mask i j (k + 1)) current .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
  simp only [expSelectEnv, expInnerEnv, paramsEnv]
  rw [← ofNat_succ]
  rfl

private theorem exec_expSelectBody {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word bit mask : U256)
    (i j k : Nat) :
    ExecStmt D funs
      (expSelectEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word bit mask i j k) current (.block expSelectBody)
      (expSelectEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word bit mask i j k) (selectLimbStep mask k current) .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 150)
  rfl

private theorem exec_expSelectLoop {funs : FunEnv D} (initial : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word bit mask : U256)
    (i j : Nat) :
    ∀ (remaining k : Nat), k + remaining = n.toNat →
      ExecLoop D funs
        (expSelectEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          word bit mask i j k) (selectLimbPrefix mask k initial)
        (yulE% lt(k, n)) (yul% { k := add(k, 1) }) expSelectBody
        (expSelectEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          word bit mask i j n.toNat)
        (selectLimbPrefix mask n.toNat initial) .normal := by
  intro remaining
  induction remaining with
  | zero =>
      intro k hk
      have : k = n.toNat := by omega
      subst k
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal, dialect_zero,
        YulSemantics.EVM.b2w, BitVec.ult]
  | succ remaining ih =>
      intro k hk
      have hkn : k < n.toNat := by omega
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_expSelectBody (selectLimbPrefix mask k initial) bsize esize
          modulusSize baseOff expOff modOff n modulusOr word bit mask i j k)
        (Or.inl rfl)
        (exec_expIncrementK (selectLimbPrefix mask (k + 1) initial) bsize esize
          modulusSize baseOff expOff modOff n modulusOr word bit mask i j k) ?_
      · rw [dialect_zero]
        simp [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.b2w, BitVec.ult]
        rw [Nat.mod_eq_of_lt (hkn.trans n.isLt)]
        exact hkn
      · simpa [selectLimbPrefix] using ih (k + 1) (by omega)

private theorem exec_expIncrementJ {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word : U256)
    (i j : Nat) :
    ExecStmt D funs
      (expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i j) current (.block incrementJ)
      (expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i (j + 1)) current .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
  simp only [incrementJ, expInnerEnv, paramsEnv]
  rw [← ofNat_succ]
  rfl

private theorem exec_expBitBody {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word : U256)
    (i j : Nat)
    (hmul : lookupFun (hoist D expBitBody :: funs) "mulModBig" =
      lookupFun verifiedFunctions "mulModBig")
    (hcopy : lookupFun (hoist D expBitBody :: funs) "copyLimbs" =
      lookupFun verifiedFunctions "copyLimbs") :
    ExecStmt D funs
      (expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i j) current (.block expBitBody)
      (expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        word i j) (exponentBitStep n word j current) .normal := by
  let V := expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
    word i j
  let bit := baseBit word j
  let squared := BigMul.mulModBigState current 0x0800 0x0800 0x0c00 0x0000 n
  let copied := copyWordsState squared 0x0800 0x0c00 n.toNat
  let product := BigMul.mulModBigState copied 0x0800 0x0400 0x0c00 0x0000 n
  let mask : U256 := 0 - bit
  let bodyFuns : FunEnv D := hoist D expBitBody :: funs
  let selectFuns : FunEnv D := [] :: bodyFuns
  have hbit : EvalExpr D bodyFuns V current
      (yulE% and(shr(sub(7, j), w), 1)) (.vals [bit] current) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
    rfl
  have hmulArgs1 : EvalArgs D bodyFuns
      (expBitEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word
        bit i j) current
      [yulE% 0x0800, yulE% 0x0800, yulE% 0x0c00, yulE% 0x0000, yulE% n]
      (.vals [0x0800, 0x0800, 0x0c00, 0x0000, n] current) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 60)
    rfl
  have hmul1 : EvalExpr D bodyFuns
      (expBitEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word
        bit i j) current
      (yulE% mulModBig(0x0800, 0x0800, 0x0c00, 0x0000, n))
      (.vals [] squared) := by
    simpa [bodyFuns, squared, mkCall, parse] using
      (BigMul.eval_mulModBig (funs := bodyFuns) (st := current)
        (0x0800 : U256) 0x0800 0x0c00 0x0000 n (by rw [hmul]; rfl) hmulArgs1)
  have hcopyArgs : EvalArgs D bodyFuns
      (expBitEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word
        bit i j) squared [yulE% 0x0800, yulE% 0x0c00, yulE% n]
      (.vals [0x0800, 0x0c00, n] squared) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 40)
    rfl
  have hcopyCall : EvalExpr D bodyFuns
      (expBitEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word
        bit i j) squared (yulE% copyLimbs(0x0800, 0x0c00, n))
      (.vals [] copied) := by
    simpa [bodyFuns, copied, mkCall, parse] using
      (eval_copyLimbs (funs := bodyFuns) (st := squared)
        (0x0800 : U256) 0x0c00 n (by rw [hcopy]; rfl) hcopyArgs)
  have hmulArgs2 : EvalArgs D bodyFuns
      (expBitEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word
        bit i j) copied
      [yulE% 0x0800, yulE% 0x0400, yulE% 0x0c00, yulE% 0x0000, yulE% n]
      (.vals [0x0800, 0x0400, 0x0c00, 0x0000, n] copied) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 60)
    rfl
  have hmul2 : EvalExpr D bodyFuns
      (expBitEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word
        bit i j) copied
      (yulE% mulModBig(0x0800, 0x0400, 0x0c00, 0x0000, n))
      (.vals [] product) := by
    simpa [bodyFuns, product, mkCall, parse] using
      (BigMul.eval_mulModBig (funs := bodyFuns) (st := copied)
        (0x0800 : U256) 0x0400 0x0c00 0x0000 n (by rw [hmul]; rfl) hmulArgs2)
  have hmask : EvalExpr D bodyFuns
      (expBitEnv bsize esize modulusSize baseOff expOff modOff n modulusOr word
        bit i j) product (yulE% sub(0, bit)) (.vals [mask] product) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  have hselect := exec_expSelectLoop (funs := selectFuns) product bsize esize
    modulusSize baseOff expOff modOff n modulusOr word bit mask i j n.toNat 0
    (by omega)
  refine Step.block (D := D)
    (Vb := expMaskEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
      word bit mask i j) ?_
  refine Step.seqCons (Step.letVal hbit rfl) ?_
  refine Step.seqCons (Step.exprStmt hmul1) ?_
  refine Step.seqCons (Step.exprStmt hcopyCall) ?_
  refine Step.seqCons (Step.exprStmt hmul2) ?_
  refine Step.seqCons (Step.letVal hmask rfl) ?_
  refine Step.seqCons ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := expSelectEnv bsize esize modulusSize baseOff expOff modOff n
      modulusOr word bit mask i j 0) (stinit := product)
    (Vend := expSelectEnv bsize esize modulusSize baseOff expOff modOff n
      modulusOr word bit mask i j n.toNat) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · simpa [selectFuns, bodyFuns, expBitBody, expSelectBody,
      exponentBitStep, bit, squared, copied, product, mask,
      selectLimbPrefix, hoist] using hselect

private theorem exec_expBitLoop {funs : FunEnv D} (initial : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr word : U256)
    (i : Nat)
    (hmul : lookupFun funs "mulModBig" =
      lookupFun verifiedFunctions "mulModBig")
    (hcopy : lookupFun funs "copyLimbs" =
      lookupFun verifiedFunctions "copyLimbs") :
    ∀ (remaining j : Nat), j + remaining = 8 →
      ExecLoop D funs
        (expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          word i j) (exponentBitPrefix n word j initial)
        (yulE% lt(j, 8)) incrementJ expBitBody
        (expInnerEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          word i 8) (exponentBitPrefix n word 8 initial) .normal := by
  intro remaining
  induction remaining with
  | zero =>
      intro j hj
      have : j = 8 := by omega
      subst j
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl)
        ?_
      norm_num [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal, dialect_zero,
        YulSemantics.EVM.b2w, BitVec.ult, YulSemantics.EVM.litValue]
  | succ remaining ih =>
      intro j hj
      have hj8 : j < 8 := by omega
      have hmul' : lookupFun (hoist D expBitBody :: funs) "mulModBig" =
          lookupFun verifiedFunctions "mulModBig" := by
        simpa [expBitBody, hoist, lookupFun] using hmul
      have hcopy' : lookupFun (hoist D expBitBody :: funs) "copyLimbs" =
          lookupFun verifiedFunctions "copyLimbs" := by
        simpa [expBitBody, hoist, lookupFun] using hcopy
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl)
        ?_
        (exec_expBitBody (exponentBitPrefix n word j initial) bsize esize
          modulusSize baseOff expOff modOff n modulusOr word i j hmul' hcopy')
        (Or.inl rfl)
        (exec_expIncrementJ (exponentBitPrefix n word (j + 1) initial)
          bsize esize modulusSize baseOff expOff modOff n modulusOr word i j) ?_
      · rw [dialect_zero]
        simp [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.b2w, BitVec.ult,
          YulSemantics.EVM.litValue]
        have hjM : j <
            115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
          by omega
        rw [Nat.mod_eq_of_lt hjM]
        exact hj8
      · simpa [exponentBitPrefix] using ih (j + 1) (by omega)

private theorem exec_expOuterBody {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr : U256)
    (i : Nat)
    (hmul : lookupFun funs "mulModBig" =
      lookupFun verifiedFunctions "mulModBig")
    (hcopy : lookupFun funs "copyLimbs" =
      lookupFun verifiedFunctions "copyLimbs")
    (hbyte : lookupFun (hoist D expOuterBody :: funs) "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ExecStmt D funs
      (expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
      current (.block expOuterBody)
      (expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
      (exponentByteStep expOff n i current) .normal := by
  let V := expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i
  let off := expOff + BitVec.ofNat 256 i
  let word := StateModel.calldataByteValue current off
  let bodyFuns : FunEnv D := hoist D expOuterBody :: funs
  let loopFuns : FunEnv D := [] :: bodyFuns
  have hoff : EvalExpr D bodyFuns V current (yulE% add(expOff, i))
      (.vals [off] current) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  have hw : EvalExpr D bodyFuns V current
      (yulE% calldataByte(add(expOff, i))) (.vals [word] current) := by
    simpa [bodyFuns, word, off, mkCall, parse] using
      (eval_calldataByte off hbyte hoff)
  have hmul' : lookupFun loopFuns "mulModBig" =
      lookupFun verifiedFunctions "mulModBig" := by
    simpa [loopFuns, bodyFuns, expOuterBody, hoist, lookupFun] using hmul
  have hcopy' : lookupFun loopFuns "copyLimbs" =
      lookupFun verifiedFunctions "copyLimbs" := by
    simpa [loopFuns, bodyFuns, expOuterBody, hoist, lookupFun] using hcopy
  have hbits := exec_expBitLoop (funs := loopFuns) current bsize esize
    modulusSize baseOff expOff modOff n modulusOr word i hmul' hcopy' 8 0 (by omega)
  refine Step.block (D := D)
    (Vb := ("w", word) ::
      expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i) ?_
  refine Step.seqCons (Step.letVal hw rfl) ?_
  refine Step.seqCons ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := expInnerEnv bsize esize modulusSize baseOff expOff modOff n
      modulusOr word i 0) (stinit := current)
    (Vend := expInnerEnv bsize esize modulusSize baseOff expOff modOff n
      modulusOr word i 8) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · simpa [loopFuns, bodyFuns, expOuterBody, expBitBody, incrementJ,
      exponentByteStep, exponentBitPrefix, word, off, hoist] using hbits

private theorem exec_expIncrementI {funs : FunEnv D} (current : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr : U256)
    (i : Nat) :
    ExecStmt D funs
      (expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
      current (.block incrementI)
      (expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
        (i + 1)) current .normal := by
  simpa [expOuterEnv, baseOuterEnv] using
    (exec_incrementI (funs := funs) current bsize esize modulusSize baseOff
      expOff modOff n modulusOr i)

theorem exec_exponentLoop {funs : FunEnv D} (initial : EvmState)
    (bsize esize modulusSize baseOff expOff modOff n modulusOr : U256)
    (hmul : lookupFun funs "mulModBig" =
      lookupFun verifiedFunctions "mulModBig")
    (hcopy : lookupFun funs "copyLimbs" =
      lookupFun verifiedFunctions "copyLimbs")
    (hbyte : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions)) :
    ∀ (remaining i : Nat), i + remaining = esize.toNat →
      ExecLoop D funs
        (expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr i)
        (exponentBytePrefix expOff n i initial)
        (yulE% lt(i, esize)) incrementI expOuterBody
        (expOuterEnv bsize esize modulusSize baseOff expOff modOff n modulusOr
          esize.toNat)
        (exponentBytePrefix expOff n esize.toNat initial) .normal := by
  intro remaining
  induction remaining with
  | zero =>
      intro i hi
      have : i = esize.toNat := by omega
      subst i
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal, dialect_zero,
        YulSemantics.EVM.b2w, BitVec.ult]
  | succ remaining ih =>
      intro i hi
      have hie : i < esize.toNat := by omega
      have hbyte' : lookupFun (hoist D expOuterBody :: funs) "calldataByte" =
          some (calldataByteDecl, verifiedFunctions) := by
        simpa [expOuterBody, hoist, lookupFun] using hbyte
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_expOuterBody (exponentBytePrefix expOff n i initial)
          bsize esize modulusSize baseOff expOff modOff n modulusOr i
          hmul hcopy hbyte') (Or.inl rfl)
        (exec_expIncrementI (exponentBytePrefix expOff n (i + 1) initial)
          bsize esize modulusSize baseOff expOff modOff n modulusOr i) ?_
      · rw [dialect_zero]
        simp [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.b2w, BitVec.ult]
        rw [Nat.mod_eq_of_lt (hie.trans esize.isLt)]
        exact hie
      · simpa [exponentBytePrefix] using ih (i + 1) (by omega)

def serializedResultState (st : EvmState) (modulusSize : U256) : EvmState :=
  serializePrefix modulusSize modulusSize.toNat st

def returnedResultState (st : EvmState) (modulusSize : U256) : EvmState :=
  let serialized := serializedResultState st modulusSize
  { touchMemory serialized 0x1800 modulusSize.toNat with
    halted := some (.ret,
      readBytes serialized.memory 0x1800 modulusSize.toNat) }

/-- Once the big exponent loop has established its exact result state, the
source serializer and return compose without any arithmetic assumptions. -/
theorem exec_serializeReturn (funs : FunEnv D) (V : VEnv D) (st : EvmState)
    (modulusSize : U256)
    (hmodulus : VEnv.get V "modulusSize" = some modulusSize)
    (_hi : VEnv.get V "i" = none) :
    ExecStmts D funs V st
      (yul% {
        for { let i := 0 } lt(i, modulusSize) { i := add(i, 1) } {
          let reverse := sub(sub(modulusSize, 1), i)
          let limb := div(reverse, 32)
          let shift := mul(mod(reverse, 32), 8)
          mstore8(add(0x1800, i),
            and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff))
        }
        return(0x1800, modulusSize)
      }) V (returnedResultState st modulusSize) .halt := by
  let serialized := serializedResultState st modulusSize
  let loopFuns : FunEnv D := [] :: funs
  have hloop := exec_serializeLoop (funs := loopFuns) V st modulusSize hmodulus
  have hret : EvalExpr D funs V serialized
      (mkCall "return" [.lit (.number 0x1800), .var "modulusSize"])
      (.halt (returnedResultState st modulusSize)) := by
    apply Step.builtinHalt (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var hmodulus)) Step.lit)
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.litValue,
      returnedResultState, serialized]
  refine Step.seqCons (D := D) (V1 := V) (st1 := serialized) ?_ ?_
  · have hfor : ExecStmt D funs V st
        (.forLoop (yul% { let i := 0 }) (yulE% lt(i, modulusSize))
          Challenge.Modexp.Reference.Proofs.Yul.incrementI
          Challenge.Modexp.Reference.Proofs.Yul.serializeBody)
        (restore V (("i", BitVec.ofNat 256 modulusSize.toNat) :: V))
        serialized .normal := by
      refine Step.forLoop (D := D)
        (Vinit := ("i", 0) :: V) (stinit := st)
        (Vend := ("i", BitVec.ofNat 256 modulusSize.toNat) :: V) ?_ ?_
      · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
      · simpa [loopFuns, serialized, serializedResultState, hoist] using hloop
    have hrestore : restore V (("i", BitVec.ofNat 256 modulusSize.toNat) :: V) = V := by
      simp [restore, _hi]
    rw [hrestore] at hfor
    simpa [Challenge.Modexp.Reference.Proofs.Yul.incrementI,
      Challenge.Modexp.Reference.Proofs.Yul.serializeBody] using hfor
  exact Step.seqStop (Step.exprStmtHalt hret) (by decide)

/-- Direct execution from the initialized accumulator through every exponent
byte and bit, branchless limb selection, serialization, and return. -/
theorem exec_exponentAndReturn (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256) :
    let n := limbCount modulusSize
    let modulusOr := modulusOrValue st modulusSize modOff
    let V := ("modulusOr", modulusOr) :: ("n", n) ::
      paramsEnv bsize esize modulusSize baseOff expOff modOff
    let initial := initializedAccumulatorState st bsize modulusSize baseOff modOff
    let exponentiated := exponentiatedState st bsize esize modulusSize baseOff
      expOff modOff
    ExecStmts D ([] :: verifiedFunctions) V initial
      (yul% {
        for { let i := 0 } lt(i, esize) { i := add(i, 1) } {
          let w := calldataByte(add(expOff, i))
          for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
            let bit := and(shr(sub(7, j), w), 1)
            mulModBig(0x0800, 0x0800, 0x0c00, 0x0000, n)
            copyLimbs(0x0800, 0x0c00, n)
            mulModBig(0x0800, 0x0400, 0x0c00, 0x0000, n)
            let mask := sub(0, bit)
            for { let k := 0 } lt(k, n) { k := add(k, 1) } {
              let off := mul(k, 32)
              let square := mload(add(0x0800, off))
              let product := mload(add(0x0c00, off))
              mstore(add(0x0800, off),
                xor(square, and(xor(square, product), mask)))
            }
          }
        }
        for { let i := 0 } lt(i, modulusSize) { i := add(i, 1) } {
          let reverse := sub(sub(modulusSize, 1), i)
          let limb := div(reverse, 32)
          let shift := mul(mod(reverse, 32), 8)
          mstore8(add(0x1800, i),
            and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff))
        }
        return(0x1800, modulusSize)
      }) V (returnedResultState exponentiated modulusSize) .halt := by
  dsimp only
  let n := limbCount modulusSize
  let modulusOr := modulusOrValue st modulusSize modOff
  let V := ("modulusOr", modulusOr) :: ("n", n) ::
    paramsEnv bsize esize modulusSize baseOff expOff modOff
  let initial := initializedAccumulatorState st bsize modulusSize baseOff modOff
  let exponentiated := exponentiatedState st bsize esize modulusSize baseOff
    expOff modOff
  let bodyFuns : FunEnv D := [] :: verifiedFunctions
  let loopFuns : FunEnv D := [] :: bodyFuns
  have hmul : lookupFun loopFuns "mulModBig" =
      lookupFun verifiedFunctions "mulModBig" := by rfl
  have hcopy : lookupFun loopFuns "copyLimbs" =
      lookupFun verifiedFunctions "copyLimbs" := by rfl
  have hbyte : lookupFun loopFuns "calldataByte" =
      some (calldataByteDecl, verifiedFunctions) := by rfl
  have hexp := exec_exponentLoop (funs := loopFuns) initial bsize esize
    modulusSize baseOff expOff modOff n modulusOr hmul hcopy hbyte
    esize.toNat 0 (by omega)
  have htail := exec_serializeReturn bodyFuns V exponentiated modulusSize
    (by rfl) (by rfl)
  refine Step.seqCons (D := D) (V1 := V) (st1 := exponentiated) ?_ ?_
  · refine Step.forLoop (D := D)
      (Vinit := expOuterEnv bsize esize modulusSize baseOff expOff modOff n
        modulusOr 0) (stinit := initial)
      (Vend := expOuterEnv bsize esize modulusSize baseOff expOff modOff n
        modulusOr esize.toNat) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa [loopFuns, expOuterEnv, expOuterBody, incrementI, exponentiated,
        exponentiatedState, exponentBytePrefix, n, initial, hoist] using hexp
  simpa using htail

private theorem execStmts_append_normal {funs : FunEnv D}
    {V V1 V2 : VEnv D} {st st1 st2 : EvmState}
    {first second : Block Op} {o : Outcome}
    (hfirst : ExecStmts D funs V st first V1 st1 .normal)
    (hsecond : ExecStmts D funs V1 st1 second V2 st2 o) :
    ExecStmts D funs V st (first ++ second) V2 st2 o := by
  induction first generalizing V V1 st st1 with
  | nil =>
      cases hfirst
      simpa using hsecond
  | cons stmt rest ih =>
      cases hfirst with
      | seqCons hstmt hrest =>
          simpa using Step.seqCons hstmt (ih hrest hsecond)
      | seqStop _ hne => exact (hne rfl).elim

/-- Exact nonzero suffix, from the already scanned modulus through base
conversion, exponentiation, serialization, and return. -/
theorem exec_nonzeroSuffix (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hnonzero : modulusOrValue st modulusSize modOff ≠ 0) :
    let n := limbCount modulusSize
    let modulusOr := modulusOrValue st modulusSize modOff
    let V := ("modulusOr", modulusOr) :: ("n", n) ::
      paramsEnv bsize esize modulusSize baseOff expOff modOff
    ExecStmts D ([] :: verifiedFunctions) V
      (scannedModulusState st modulusSize modOff)
      (yul% {
        clearLimbs(0x0c00, n)
        mstore(0x0c00, 1)
        for { let i := 0 } lt(i, bsize) { i := add(i, 1) } {
          let w := calldataByte(add(baseOff, i))
          for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
            addMaskedMod(0x0400, 0x0400, 1, 0x0000, n)
            addMaskedMod(0x0400, 0x0c00,
              and(shr(sub(7, j), w), 1), 0x0000, n)
          }
        }
        addMaskedMod(0x0800, 0x0c00, 1, 0x0000, n)
        for { let i := 0 } lt(i, esize) { i := add(i, 1) } {
          let w := calldataByte(add(expOff, i))
          for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
            let bit := and(shr(sub(7, j), w), 1)
            mulModBig(0x0800, 0x0800, 0x0c00, 0x0000, n)
            copyLimbs(0x0800, 0x0c00, n)
            mulModBig(0x0800, 0x0400, 0x0c00, 0x0000, n)
            let mask := sub(0, bit)
            for { let k := 0 } lt(k, n) { k := add(k, 1) } {
              let off := mul(k, 32)
              let square := mload(add(0x0800, off))
              let product := mload(add(0x0c00, off))
              mstore(add(0x0800, off),
                xor(square, and(xor(square, product), mask)))
            }
          }
        }
        for { let i := 0 } lt(i, modulusSize) { i := add(i, 1) } {
          let reverse := sub(sub(modulusSize, 1), i)
          let limb := div(reverse, 32)
          let shift := mul(mod(reverse, 32), 8)
          mstore8(add(0x1800, i),
            and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff))
        }
        return(0x1800, modulusSize)
      }) V (returnedResultState
        (exponentiatedState st bsize esize modulusSize baseOff expOff modOff)
        modulusSize) .halt := by
  dsimp only
  have hpre := exec_nonzeroPrelude st bsize esize modulusSize baseOff expOff
    modOff hnonzero
  have htail := exec_exponentAndReturn st bsize esize modulusSize baseOff expOff
    modOff
  simpa using execStmts_append_normal hpre htail

private theorem exec_modexpBigBody_nonzero (st : EvmState)
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hnonzero : modulusOrValue st modulusSize modOff ≠ 0) :
    ExecStmt D verifiedFunctions
      (paramsEnv bsize esize modulusSize baseOff expOff modOff) st
      (.block modexpBigDecl.body)
      (paramsEnv bsize esize modulusSize baseOff expOff modOff)
      (returnedResultState
        (exponentiatedState st bsize esize modulusSize baseOff expOff modOff)
        modulusSize) .halt := by
  let n := limbCount modulusSize
  let Vparams := paramsEnv bsize esize modulusSize baseOff expOff modOff
  let Vn : VEnv D := ("n", n) :: Vparams
  let Vscan : VEnv D :=
    ("modulusOr", modulusOrValue st modulusSize modOff) :: Vn
  let s0 := clearedModulusState st modulusSize
  let s1 := clearedBaseState st modulusSize
  let s2 := clearedAccumulatorState st modulusSize
  let s3 := clearedOutputState st modulusSize
  let s4 := loadedModulusState st modulusSize modOff
  let s5 := scannedModulusState st modulusSize modOff
  let bodyFuns : FunEnv D := hoist D modexpBigDecl.body :: verifiedFunctions
  let scanFuns : FunEnv D := [] :: bodyFuns
  have hn : EvalExpr D bodyFuns Vparams st
      (yulE% div(add(modulusSize, 31), 32)) (.vals [n] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 40)
    rfl
  have hclear0 : EvalExpr D bodyFuns Vn st (yulE% clearLimbs(0x0000, n))
      (.vals [] s0) := by
    simpa [bodyFuns, Vn, s0, clearedModulusState, n, limbCount, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := st)
        (ptr := (0x0000 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hclear1 : EvalExpr D bodyFuns Vn s0 (yulE% clearLimbs(0x0400, n))
      (.vals [] s1) := by
    simpa [bodyFuns, Vn, s0, s1, clearedBaseState, n, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := s0)
        (ptr := (0x0400 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hclear2 : EvalExpr D bodyFuns Vn s1 (yulE% clearLimbs(0x0800, n))
      (.vals [] s2) := by
    simpa [bodyFuns, Vn, s1, s2, clearedAccumulatorState, n, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := s1)
        (ptr := (0x0800 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hclear3 : EvalExpr D bodyFuns Vn s2 (yulE% clearLimbs(0x1800, n))
      (.vals [] s3) := by
    simpa [bodyFuns, Vn, s2, s3, clearedOutputState, n, mkCall, parse] using
      (eval_clearLimbs (funs := bodyFuns) (V := Vn) (st := s2)
        (ptr := (0x1800 : U256)) n (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 20)
          rfl))
  have hload : EvalExpr D bodyFuns Vn s3
      (yulE% loadBigEndian(modOff, modulusSize, 0x0000)) (.vals [] s4) := by
    simpa [bodyFuns, Vn, s3, s4, loadedModulusState, mkCall, parse] using
      (eval_loadBigEndian (funs := bodyFuns) (V := Vn) (st := s3)
        modOff modulusSize (0x0000 : U256) (by rfl)
        (by
          apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful
            (fuel := 30)
          rfl))
  have hscan := exec_modulusScanLoop (funs := scanFuns) Vparams s4 n
  have hcond : EvalExpr D bodyFuns Vscan s5 (yulE% iszero(modulusOr))
      (.vals [(0 : U256)] s5) := by
    apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil (Step.var rfl))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un, YulSemantics.EVM.b2w,
      Vscan, hnonzero]
    exact hnonzero
  have hif : ExecStmt D bodyFuns Vscan s5
      (.cond (yulE% iszero(modulusOr))
        (yul% { return(0x1800, modulusSize) })) Vscan s5 .normal :=
    Step.ifFalse (D := D) hcond rfl
  have htail := exec_nonzeroSuffix st bsize esize modulusSize baseOff expOff
    modOff hnonzero
  simp only [modexpBigDecl]
  refine Step.block (D := D) (Vb := Vscan) ?_
  refine Step.seqCons (D := D) (Step.letVal hn rfl) ?_
  refine Step.seqCons (Step.exprStmt hclear0) ?_
  refine Step.seqCons (Step.exprStmt hclear1) ?_
  refine Step.seqCons (Step.exprStmt hclear2) ?_
  refine Step.seqCons (Step.exprStmt hclear3) ?_
  refine Step.seqCons (Step.exprStmt hload) ?_
  refine Step.seqCons (Step.letVal Step.lit rfl) ?_
  refine Step.seqCons (D := D) (V1 := Vscan) (st1 := s5) ?_ ?_
  · refine Step.forLoop (D := D)
      (Vinit := Challenge.Modexp.Reference.Proofs.Yul.scanEnv n Vparams 0 0)
      (stinit := s4)
      (Vend := Challenge.Modexp.Reference.Proofs.Yul.scanEnv n Vparams n.toNat
        (modulusOrValue st modulusSize modOff)) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa only [scanFuns, bodyFuns, modexpBigDecl, hoist, List.filterMap,
        Challenge.Modexp.Reference.Proofs.Yul.incrementI,
        Challenge.Modexp.Reference.Proofs.Yul.modulusScanBody,
        Vscan, Vn, s4, s5, scannedModulusState, modulusOrValue, n] using hscan
  refine Step.seqCons hif ?_
  simpa [bodyFuns, modexpBigDecl, hoist] using htail

/-- Complete relational contract for the nonzero source big path. -/
theorem eval_modexpBig_nonzero {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)}
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hlookup : lookupFun funs "modexpBig" =
      some (modexpBigDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args
      (.vals [bsize, esize, modulusSize, baseOff, expOff, modOff] st1))
    (hnonzero : modulusOrValue st1 modulusSize modOff ≠ 0) :
    EvalExpr D funs V st (.call "modexpBig" args)
      (.halt (returnedResultState
        (exponentiatedState st1 bsize esize modulusSize baseOff expOff modOff)
        modulusSize)) := by
  exact Step.callHalt (D := D) hargs hlookup rfl
    (exec_modexpBigBody_nonzero st1 bsize esize modulusSize baseOff expOff modOff
      hnonzero)

/-- Lookup-specialized nonzero contract for calls from the verified MODEXP
program. -/
theorem eval_modexpBig_nonzero_verified {V : VEnv D} {st st1 : EvmState}
    {args : List (Expr Op)}
    (bsize esize modulusSize baseOff expOff modOff : U256)
    (hargs : EvalArgs D verifiedFunctions V st args
      (.vals [bsize, esize, modulusSize, baseOff, expOff, modOff] st1))
    (hnonzero : modulusOrValue st1 modulusSize modOff ≠ 0) :
    EvalExpr D verifiedFunctions V st (.call "modexpBig" args)
      (.halt (returnedResultState
        (exponentiatedState st1 bsize esize modulusSize baseOff expOff modOff)
        modulusSize)) := by
  exact eval_modexpBig_nonzero bsize esize modulusSize baseOff expOff modOff
    lookup_modexpBig hargs hnonzero

end Challenge.Modexp.Reference.Proofs.Yul.BigPath
