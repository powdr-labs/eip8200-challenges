import Challenge.Modexp.Reference.Proofs.Yul.BigArithmetic
import Challenge.YulProof.Interpreter

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Direct source-Yul contract for `mulModBig`

The executable recurrence mirrors the source's outer limb loop and its fixed
256-bit inner loop.  Arithmetic interpretation is deliberately left to a
later bridge to `Algorithm.mulBits`.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigMul

open YulSemantics
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open Challenge.YulProof.Interpreter

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

/-- One bit of the little-endian multiplier limb, as selected by the Yul. -/
def multiplierBit (word : U256) (j : Nat) : U256 :=
  (word >>> (BitVec.ofNat 256 j).toNat) &&& 1

/-- One inner double-and-add step, expressed through the already certified
exact post-state of `addMaskedMod`. -/
def mulBitStep (out modulus n word : U256) (j : Nat) (st : EvmState) : EvmState :=
  let afterAdd := BigArithmetic.addMaskedModState st out 0x1000
    (multiplierBit word j) modulus n.toNat
  BigArithmetic.addMaskedModState afterAdd 0x1000 0x1000 1 modulus n.toNat

def mulBitPrefix (out modulus n word : U256) : Nat → EvmState → EvmState
  | 0, st => st
  | j + 1, st => mulBitStep out modulus n word j
      (mulBitPrefix out modulus n word j st)

def mulLimbStep (b out modulus n : U256) (i : Nat) (st : EvmState) : EvmState :=
  let address := wordOffset b i
  let word := loadWord st.memory address.toNat
  let loaded := touchMemory st address.toNat 32
  mulBitPrefix out modulus n word 256 loaded

def mulLimbPrefix (b out modulus n : U256) : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st => mulLimbStep b out modulus n i
      (mulLimbPrefix b out modulus n i st)

/-- Exact intended post-state of the complete source helper. -/
def mulModBigState (st : EvmState) (a b out modulus n : U256) : EvmState :=
  let cleared := clearWordsState st out n.toNat
  let copied := copyWordsState cleared 0x1000 a n.toNat
  mulLimbPrefix b out modulus n n.toNat copied

private theorem dialect_zero : D.zero = (0 : U256) := rfl

private def mulModBigDecl : FDecl D where
  params := ["a", "b", "out", "modulus", "n"]
  rets := []
  body := yul% {
    clearLimbs(out, n)
    copyLimbs(0x1000, a, n)
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let w := mload(add(b, mul(i, 32)))
      for { let j := 0 } lt(j, 256) { j := add(j, 1) } {
        let bit := and(shr(j, w), 1)
        addMaskedMod(out, 0x1000, bit, modulus, n)
        addMaskedMod(0x1000, 0x1000, 1, modulus, n)
      }
    }
  }

private theorem lookup_mulModBig :
    lookupFun verifiedFunctions "mulModBig" =
      some (mulModBigDecl, verifiedFunctions) := by
  rfl

private def params (a b out modulus n : U256) : VEnv D :=
  [("a", a), ("b", b), ("out", out), ("modulus", modulus), ("n", n)]

private def outerEnv (a b out modulus n : U256) (i : Nat) : VEnv D :=
  [("i", BitVec.ofNat 256 i)] ++ params a b out modulus n

private def innerEnv (a b out modulus n word : U256) (i j : Nat) : VEnv D :=
  [("j", BitVec.ofNat 256 j), ("w", word), ("i", BitVec.ofNat 256 i)] ++
    params a b out modulus n

private def incrementI : Block Op := yul% { i := add(i, 1) }
private def incrementJ : Block Op := yul% { j := add(j, 1) }

private def innerBody : Block Op := yul% {
  let bit := and(shr(j, w), 1)
  addMaskedMod(out, 0x1000, bit, modulus, n)
  addMaskedMod(0x1000, 0x1000, 1, modulus, n)
}

private def outerBody : Block Op := yul% {
  let w := mload(add(b, mul(i, 32)))
  for { let j := 0 } lt(j, 256) { j := add(j, 1) } {
    let bit := and(shr(j, w), 1)
    addMaskedMod(out, 0x1000, bit, modulus, n)
    addMaskedMod(0x1000, 0x1000, 1, modulus, n)
  }
}

private theorem ofNat_succ (i : Nat) :
    BitVec.ofNat 256 i + 1 = BitVec.ofNat 256 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

private theorem exec_incrementI {funs : FunEnv D} (st : EvmState)
    (a b out modulus n : U256) (i : Nat) :
    ExecStmt D funs (outerEnv a b out modulus n i) st (.block incrementI)
      (outerEnv a b out modulus n (i + 1)) st .normal := by
  have h : ExecStmt D funs (outerEnv a b out modulus n i) st (.block incrementI)
      (("i", BitVec.ofNat 256 i + 1) :: params a b out modulus n) st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ] at h
  simpa [outerEnv] using h

private theorem exec_incrementJ {funs : FunEnv D} (st : EvmState)
    (a b out modulus n word : U256) (i j : Nat) :
    ExecStmt D funs (innerEnv a b out modulus n word i j) st (.block incrementJ)
      (innerEnv a b out modulus n word i (j + 1)) st .normal := by
  have h : ExecStmt D funs (innerEnv a b out modulus n word i j) st (.block incrementJ)
      (("j", BitVec.ofNat 256 j + 1) ::
        [("w", word), ("i", BitVec.ofNat 256 i)] ++ params a b out modulus n)
      st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rw [ofNat_succ] at h
  simpa [innerEnv] using h

private theorem exec_innerBody {funs : FunEnv D} (st : EvmState)
    (a b out modulus n word : U256) (i j : Nat)
    (hlookup : lookupFun (hoist D innerBody :: funs) "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod") :
    ExecStmt D funs (innerEnv a b out modulus n word i j) st
      (.block innerBody) (innerEnv a b out modulus n word i j)
      (mulBitStep out modulus n word j st) .normal := by
  let bit := multiplierBit word j
  let afterAdd := BigArithmetic.addMaskedModState st out 0x1000 bit modulus n.toNat
  let bodyFuns := hoist D innerBody :: funs
  have hbit : EvalExpr D bodyFuns (innerEnv a b out modulus n word i j) st
      (yulE% and(shr(j, w), 1)) (.vals [bit] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 40)
    rfl
  have hargs1 : EvalArgs D bodyFuns
      (("bit", bit) :: innerEnv a b out modulus n word i j) st
      [yulE% out, yulE% 0x1000, yulE% bit, yulE% modulus, yulE% n]
      (.vals [out, 0x1000, bit, modulus, n] st) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 80)
    rfl
  have hadd1 := BigArithmetic.eval_addMaskedMod out 0x1000 bit modulus n
    (by rw [hlookup]; rfl) hargs1
  have hargs2 : EvalArgs D bodyFuns
      (("bit", bit) :: innerEnv a b out modulus n word i j) afterAdd
      [yulE% 0x1000, yulE% 0x1000, yulE% 1, yulE% modulus, yulE% n]
      (.vals [0x1000, 0x1000, 1, modulus, n] afterAdd) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 80)
    rfl
  have hadd2 := BigArithmetic.eval_addMaskedMod 0x1000 0x1000 1 modulus n
    (by rw [hlookup]; rfl) hargs2
  refine Step.block (D := D)
    (Vb := ("bit", bit) :: innerEnv a b out modulus n word i j) ?_
  refine Step.seqCons (Step.letVal hbit rfl) ?_
  refine Step.seqCons (Step.exprStmt hadd1) ?_
  refine Step.seqCons (Step.exprStmt hadd2) Step.seqNil

private theorem exec_innerLoop {funs : FunEnv D} (st : EvmState)
    (a b out modulus n word : U256) (i : Nat)
    (hlookup : lookupFun funs "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod") :
    ∀ (k j : Nat), j + k = 256 →
      ExecLoop D funs
        (innerEnv a b out modulus n word i j)
        (mulBitPrefix out modulus n word j st)
        (yulE% lt(j, 256)) incrementJ innerBody
        (innerEnv a b out modulus n word i 256)
        (mulBitPrefix out modulus n word 256 st) .normal := by
  intro k
  induction k with
  | zero =>
      intro j hj
      have : j = 256 := by omega
      subst j
      refine Step.loopDone
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl) ?_
      simp only [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal]
      norm_num [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult,
        YulSemantics.EVM.litValue]
  | succ k ih =>
      intro j hj
      have hj256 : j < 256 := by omega
      have hlookup' : lookupFun (hoist D innerBody :: funs) "addMaskedMod" =
          lookupFun verifiedFunctions "addMaskedMod" := by
        simpa [innerBody, hoist, lookupFun] using hlookup
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)) rfl) ?_
        (exec_innerBody (mulBitPrefix out modulus n word j st)
          a b out modulus n word i j hlookup') (Or.inl rfl)
        (exec_incrementJ (mulBitPrefix out modulus n word (j + 1) st)
          a b out modulus n word i j) ?_
      · simp only [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal]
        simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult,
          YulSemantics.EVM.litValue,
          Nat.mod_eq_of_lt (by omega : j < 2 ^ 256), hj256]
        rw [Nat.mod_eq_of_lt (by omega :
          j < 115792089237316195423570985008687907853269984665640564039457584007913129639936)]
        exact hj256
      · simpa [mulBitPrefix] using ih (j + 1) (by omega)

private theorem exec_outerBody {funs : FunEnv D} (st : EvmState)
    (a b out modulus n : U256) (i : Nat)
    (hlookup : lookupFun funs "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod") :
    ExecStmt D funs (outerEnv a b out modulus n i) st (.block outerBody)
      (outerEnv a b out modulus n i) (mulLimbStep b out modulus n i st) .normal := by
  let address := wordOffset b i
  let word := loadWord st.memory address.toNat
  let loaded := touchMemory st address.toNat 32
  let bodyFuns := hoist D outerBody :: funs
  have hw : EvalExpr D bodyFuns (outerEnv a b out modulus n i) st
      (yulE% mload(add(b, mul(i, 32)))) (.vals [word] loaded) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 60)
    rfl
  have hlookup' : lookupFun
      (hoist D [Stmt.letDecl ["j"] (some (.lit (.number 0)))] :: bodyFuns)
      "addMaskedMod" = lookupFun verifiedFunctions "addMaskedMod" := by
    simpa [bodyFuns, outerBody, hoist, lookupFun] using hlookup
  refine Step.block (D := D)
    (Vb := ("w", word) :: outerEnv a b out modulus n i) ?_
  refine Step.seqCons (Step.letVal hw rfl) ?_
  refine Step.seqCons ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := innerEnv a b out modulus n word i 0) (stinit := loaded)
    (Vend := innerEnv a b out modulus n word i 256) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · simpa [bodyFuns, outerBody, innerEnv, innerBody, incrementJ, hoist,
      mulBitPrefix, mulLimbStep, address, word, loaded] using
      exec_innerLoop
        (funs := hoist D [Stmt.letDecl ["j"] (some (.lit (.number 0)))] ::
          bodyFuns)
        loaded a b out modulus n word i hlookup' 256 0 (by omega)

private theorem exec_outerLoop {funs : FunEnv D} (st : EvmState)
    (a b out modulus n : U256)
    (hlookup : lookupFun funs "addMaskedMod" =
      lookupFun verifiedFunctions "addMaskedMod") :
    ∀ (k i : Nat), i + k = n.toNat →
      ExecLoop D funs
        (outerEnv a b out modulus n i) (mulLimbPrefix b out modulus n i st)
        (yulE% lt(i, n)) incrementI outerBody
        (outerEnv a b out modulus n n.toNat)
        (mulLimbPrefix b out modulus n n.toNat st) .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have : i = n.toNat := by omega
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
      have hlookup' : lookupFun (hoist D outerBody :: funs) "addMaskedMod" =
          lookupFun verifiedFunctions "addMaskedMod" := by
        simpa [outerBody, hoist, lookupFun] using hlookup
      refine Step.loopStep
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_outerBody (mulLimbPrefix b out modulus n i st)
          a b out modulus n i hlookup') (Or.inl rfl)
        (exec_incrementI (mulLimbPrefix b out modulus n (i + 1) st)
          a b out modulus n i) ?_
      · simp only [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal]
        simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult,
          Nat.mod_eq_of_lt (hin.trans n.isLt), hin]
      · simpa [mulLimbPrefix] using ih (i + 1) (by omega)

private theorem exec_mulModBigBody (st : EvmState)
    (a b out modulus n : U256) :
    ExecStmt D verifiedFunctions (params a b out modulus n) st
      (.block mulModBigDecl.body) (params a b out modulus n)
      (mulModBigState st a b out modulus n) .normal := by
  let cleared := clearWordsState st out n.toNat
  let copied := copyWordsState cleared 0x1000 a n.toNat
  let bodyFuns := hoist D mulModBigDecl.body :: verifiedFunctions
  have hclearArgs : EvalArgs D bodyFuns (params a b out modulus n) st
      [yulE% out, yulE% n] (.vals [out, n] st) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  have hclear := Procedures.eval_clearLimbs out n (by rfl) hclearArgs
  have hcopyArgs : EvalArgs D bodyFuns (params a b out modulus n) cleared
      [yulE% 0x1000, yulE% a, yulE% n] (.vals [0x1000, a, n] cleared) := by
    apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 40)
    rfl
  have hcopy := Procedures.eval_copyLimbs 0x1000 a n (by rfl) hcopyArgs
  have hlookup : lookupFun
      (hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] :: bodyFuns)
      "addMaskedMod" = lookupFun verifiedFunctions "addMaskedMod" := by
    rfl
  refine Step.block (D := D) (Vb := params a b out modulus n) ?_
  refine Step.seqCons (Step.exprStmt hclear) ?_
  refine Step.seqCons (Step.exprStmt hcopy) ?_
  refine Step.seqCons ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := outerEnv a b out modulus n 0) (stinit := copied)
    (Vend := outerEnv a b out modulus n n.toNat) ?_ ?_
  · exact Step.seqCons (Step.letVal Step.lit rfl) Step.seqNil
  · simpa [bodyFuns, mulModBigDecl, outerEnv, outerBody, incrementI,
      mulLimbPrefix, mulModBigState, cleared, copied, hoist] using
      exec_outerLoop
        (funs := hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] ::
          bodyFuns)
        copied a b out modulus n hlookup n.toNat 0 (by omega)

/-- Direct relational contract for the source `mulModBig` helper. -/
theorem eval_mulModBig {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)} (a b out modulus n : U256)
    (hlookup : lookupFun funs "mulModBig" =
      some (mulModBigDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args
      (.vals [a, b, out, modulus, n] st1)) :
    EvalExpr D funs V st (.call "mulModBig" args)
      (.vals [] (mulModBigState st1 a b out modulus n)) := by
  refine Step.callOk (D := D) (Vend := params a b out modulus n)
    hargs hlookup rfl (exec_mulModBigBody st1 a b out modulus n) (Or.inl rfl)

/-- Lookup-specialized contract for calls from the verified program. -/
theorem eval_mulModBig_verified {V : VEnv D} {st st1 : EvmState}
    {args : List (Expr Op)} (a b out modulus n : U256)
    (hargs : EvalArgs D verifiedFunctions V st args
      (.vals [a, b, out, modulus, n] st1)) :
    EvalExpr D verifiedFunctions V st (.call "mulModBig" args)
      (.vals [] (mulModBigState st1 a b out modulus n)) :=
  eval_mulModBig a b out modulus n lookup_mulModBig hargs

end Challenge.Modexp.Reference.Proofs.Yul.BigMul
