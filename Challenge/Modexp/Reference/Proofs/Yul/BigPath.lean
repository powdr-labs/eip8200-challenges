import Challenge.Modexp.Reference.Proofs.Yul.Procedures
import Challenge.Modexp.Reference.Proofs.Yul.BigArithmetic
import Challenge.Modexp.Reference.Proofs.Yul.BigDriver
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
  have hscan := exec_modulusScanLoop (funs := bodyFuns) Vn s4 n
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
  refine Step.seqCons (D := D) ?_ ?_
  · refine Step.forLoop (D := D)
      (Vinit := ("i", 0) :: ("modulusOr", 0) :: Vn) (stinit := s4)
      (Vend := ("i", BitVec.ofNat 256 n.toNat) :: Vscan) ?_ ?_
    · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
    · simpa [bodyFuns, modexpBigDecl, hoist] using hscan
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

end Challenge.Modexp.Reference.Proofs.Yul.BigPath
