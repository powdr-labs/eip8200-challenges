import Challenge.Modexp.Reference.Proofs.Yul.StateModel
import Challenge.YulProof.EvmState
import Challenge.YulProof.Interpreter

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Relational contracts for MODEXP word-array procedures

The contracts in this file execute the readable source AST directly.  Their
post-states use the challenge-independent word-array transformers from
`Challenge.YulProof.EvmState`, so callers do not depend on the local layout of
the procedure environments.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.Procedures

open YulSemantics
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open Challenge.YulProof.Interpreter
open Challenge.Modexp.Reference.Proofs.Yul.StateModel

private abbrev D := Challenge.YulProof.ClosedEvm.dialect
private abbrev E := Challenge.YulProof.ClosedEvm.exec

private theorem dialect_zero : D.zero = (0 : U256) := rfl

/-- Proof-side declaration for the source `calldataByte` helper. -/
def calldataByteDecl : FDecl D where
  params := ["off"]
  rets := ["b"]
  body := yul% { b := byte(0, calldataload(off)) }

theorem lookup_calldataByte :
    lookupFun verifiedFunctions "calldataByte" =
      some (calldataByteDecl, verifiedFunctions) := by
  rfl

private theorem exec_calldataByteBody (st : EvmState) (off : U256) :
    ExecStmt D verifiedFunctions [("off", off), ("b", 0)] st
      (.block calldataByteDecl.body)
      [("off", off), ("b", calldataByteValue st off)] st .normal := by
  apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
  rfl

/-- Direct relational contract for the source `calldataByte` helper. -/
theorem eval_calldataByte {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {arg : Expr Op} (off : U256)
    (hlookup : lookupFun funs "calldataByte" =
      some (calldataByteDecl, verifiedFunctions))
    (harg : EvalExpr D funs V st arg (.vals [off] st1)) :
    EvalExpr D funs V st (.call "calldataByte" [arg])
      (.vals [calldataByteValue st1 off] st1) := by
  exact Step.callOk (D := D) (Step.argsCons Step.argsNil harg) hlookup rfl
    (exec_calldataByteBody st1 off) (Or.inl rfl)

private def clearLimbsDecl : FDecl D where
  params := ["ptr", "n"]
  rets := []
  body := yul% {
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      mstore(add(ptr, mul(i, 32)), 0)
    }
  }

private def copyLimbsDecl : FDecl D where
  params := ["dst", "src", "n"]
  rets := []
  body := yul% {
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      mstore(add(dst, mul(i, 32)), mload(add(src, mul(i, 32))))
    }
  }

private theorem lookup_clearLimbs :
    lookupFun verifiedFunctions "clearLimbs" =
      some (clearLimbsDecl, verifiedFunctions) := by
  rfl

private theorem lookup_copyLimbs :
    lookupFun verifiedFunctions "copyLimbs" =
      some (copyLimbsDecl, verifiedFunctions) := by
  rfl

private def clearBody : Block Op := yul% {
  mstore(add(ptr, mul(i, 32)), 0)
}

private def copyBody : Block Op := yul% {
  mstore(add(dst, mul(i, 32)), mload(add(src, mul(i, 32))))
}

private def increment : Block Op := yul% { i := add(i, 1) }

private theorem wordOffset_eq (base : U256) (i : Nat) :
    base + BitVec.ofNat 256 i * 32 = wordOffset base i := by
  unfold wordOffset
  apply congrArg (base + ·)
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

private theorem ofNat_succ (i : Nat) :
    BitVec.ofNat 256 i + 1 = BitVec.ofNat 256 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

private def clearEnv (ptr n : U256) (i : Nat) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("ptr", ptr), ("n", n)]

private def copyEnv (dst src n : U256) (i : Nat) : VEnv D :=
  [("i", BitVec.ofNat 256 i), ("dst", dst), ("src", src), ("n", n)]

private theorem exec_clearBody {funs : FunEnv D} (st : EvmState)
    (ptr n : U256) (i : Nat) :
    ExecStmt D funs (clearEnv ptr n i) st (.block clearBody)
      (clearEnv ptr n i) (storeWordAt st (wordOffset ptr i) 0) .normal := by
  have h : ExecStmt D funs (clearEnv ptr n i) st (.block clearBody)
      (clearEnv ptr n i)
      (storeWordAt st (ptr + BitVec.ofNat 256 i * 32) 0) .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
    rfl
  rwa [wordOffset_eq] at h

private theorem exec_copyBody {funs : FunEnv D} (st : EvmState)
    (dst src n : U256) (i : Nat) :
    ExecStmt D funs (copyEnv dst src n i) st (.block copyBody)
      (copyEnv dst src n i)
      (copyWordAt st (wordOffset dst i) (wordOffset src i)) .normal := by
  have h : ExecStmt D funs (copyEnv dst src n i) st (.block copyBody)
      (copyEnv dst src n i)
      (copyWordAt st (dst + BitVec.ofNat 256 i * 32)
        (src + BitVec.ofNat 256 i * 32)) .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 80)
    rfl
  rw [wordOffset_eq, wordOffset_eq] at h
  exact h

private theorem exec_clearIncrement {funs : FunEnv D} (st : EvmState)
    (ptr n : U256) (i : Nat) :
    ExecStmt D funs (clearEnv ptr n i) st (.block increment)
      (clearEnv ptr n (i + 1)) st .normal := by
  have h : ExecStmt D funs (clearEnv ptr n i) st (.block increment)
      [("i", BitVec.ofNat 256 i + 1), ("ptr", ptr), ("n", n)] st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rwa [ofNat_succ] at h

private theorem exec_copyIncrement {funs : FunEnv D} (st : EvmState)
    (dst src n : U256) (i : Nat) :
    ExecStmt D funs (copyEnv dst src n i) st (.block increment)
      (copyEnv dst src n (i + 1)) st .normal := by
  have h : ExecStmt D funs (copyEnv dst src n i) st (.block increment)
      [("i", BitVec.ofNat 256 i + 1), ("dst", dst), ("src", src), ("n", n)]
      st .normal := by
    apply execStmt_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 30)
    rfl
  rwa [ofNat_succ] at h

private theorem exec_clearLoop {funs : FunEnv D} (st : EvmState)
    (ptr n : U256) :
    ∀ (k i : Nat), i + k = n.toNat →
      ExecLoop D funs
        (clearEnv ptr n i) (clearWordsState st ptr i)
        (yulE% lt(i, n)) increment clearBody
        (clearEnv ptr n n.toNat) (clearWordsState st ptr n.toNat) .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = n.toNat := by omega
      subst i
      refine Step.loopDone (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp only [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal]
      simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult]
  | succ k ih =>
      intro i hi
      have hin : i < n.toNat := by omega
      refine Step.loopStep (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_clearBody (clearWordsState st ptr i) ptr n i)
        (Or.inl rfl)
        (exec_clearIncrement (clearWordsState st ptr (i + 1)) ptr n i)
        ?_
      · simp only [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal]
        simp [YulSemantics.EVM.b2w, BitVec.ult, dialect_zero,
          Nat.mod_eq_of_lt (hin.trans n.isLt), hin]
      · simpa using ih (i + 1) (by omega)

private theorem exec_copyLoop {funs : FunEnv D} (st : EvmState)
    (dst src n : U256) :
    ∀ (k i : Nat), i + k = n.toNat →
      ExecLoop D funs
        (copyEnv dst src n i) (copyWordsState st dst src i)
        (yulE% lt(i, n)) increment copyBody
        (copyEnv dst src n n.toNat) (copyWordsState st dst src n.toNat) .normal := by
  intro k
  induction k with
  | zero =>
      intro i hi
      have hieq : i = n.toNat := by omega
      subst i
      refine Step.loopDone (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
      simp only [D, Challenge.YulProof.ClosedEvm.dialect,
        YulSemantics.EVM.evmWithExternal]
      simp [dialect_zero, YulSemantics.EVM.b2w, BitVec.ult]
  | succ k ih =>
      intro i hi
      have hin : i < n.toNat := by omega
      refine Step.loopStep (D := D)
        (Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
          rfl) ?_
        (exec_copyBody (copyWordsState st dst src i) dst src n i)
        (Or.inl rfl)
        (exec_copyIncrement (copyWordsState st dst src (i + 1)) dst src n i)
        ?_
      · simp only [D, Challenge.YulProof.ClosedEvm.dialect,
          YulSemantics.EVM.evmWithExternal]
        simp [YulSemantics.EVM.b2w, BitVec.ult, dialect_zero,
          Nat.mod_eq_of_lt (hin.trans n.isLt), hin]
      · simpa using ih (i + 1) (by omega)

/-- Direct source-Yul contract for `clearLimbs`. -/
theorem eval_clearLimbs {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)} (ptr n : U256)
    (hlookup : lookupFun funs "clearLimbs" =
      some (clearLimbsDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args (.vals [ptr, n] st1)) :
    EvalExpr D funs V st (.call "clearLimbs" args)
      (.vals [] (clearWordsState st1 ptr n.toNat)) := by
  refine Step.callOk (D := D) (Vend := [("ptr", ptr), ("n", n)])
    hargs hlookup rfl ?_ (Or.inl rfl)
  simp only [clearLimbsDecl, List.zip, List.zipWith, bindZeros, List.map,
    List.append_nil]
  refine Step.block (D := D) (Vb := [("ptr", ptr), ("n", n)]) ?_
  refine Step.seqCons (D := D) ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := clearEnv ptr n 0) (stinit := st1)
    (Vend := clearEnv ptr n n.toNat) ?_ ?_
  · exact Step.seqCons (D := D) (Step.letVal Step.lit rfl) Step.seqNil
  · simpa [clearEnv, clearLimbsDecl, clearBody, increment, hoist] using
      exec_clearLoop
        (funs := hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] ::
          hoist D clearLimbsDecl.body :: verifiedFunctions)
        st1 ptr n n.toNat 0 (by omega)

/-- Direct source-Yul contract for `copyLimbs`.  The transformer deliberately
models a forward copy, including the source language's behavior for overlapping
ranges. -/
theorem eval_copyLimbs {funs : FunEnv D} {V : VEnv D}
    {st st1 : EvmState} {args : List (Expr Op)} (dst src n : U256)
    (hlookup : lookupFun funs "copyLimbs" =
      some (copyLimbsDecl, verifiedFunctions))
    (hargs : EvalArgs D funs V st args (.vals [dst, src, n] st1)) :
    EvalExpr D funs V st (.call "copyLimbs" args)
      (.vals [] (copyWordsState st1 dst src n.toNat)) := by
  refine Step.callOk (D := D)
    (Vend := [("dst", dst), ("src", src), ("n", n)])
    hargs hlookup rfl ?_ (Or.inl rfl)
  simp only [copyLimbsDecl, List.zip, List.zipWith, bindZeros, List.map,
    List.append_nil]
  refine Step.block (D := D)
    (Vb := [("dst", dst), ("src", src), ("n", n)]) ?_
  refine Step.seqCons (D := D) ?_ Step.seqNil
  refine Step.forLoop (D := D)
    (Vinit := copyEnv dst src n 0) (stinit := st1)
    (Vend := copyEnv dst src n n.toNat) ?_ ?_
  · exact Step.seqCons (D := D) (Step.letVal Step.lit rfl) Step.seqNil
  · simpa [copyEnv, copyLimbsDecl, copyBody, increment, hoist] using
      exec_copyLoop
        (funs := hoist D [Stmt.letDecl ["i"] (some (.lit (.number 0)))] ::
          hoist D copyLimbsDecl.body :: verifiedFunctions)
        st1 dst src n n.toNat 0 (by omega)

/-- Lookup-specialized contract for calls from the verified MODEXP program. -/
theorem eval_clearLimbs_verified {V : VEnv D} {st st1 : EvmState}
    {args : List (Expr Op)} (ptr n : U256)
    (hargs : EvalArgs D verifiedFunctions V st args (.vals [ptr, n] st1)) :
    EvalExpr D verifiedFunctions V st (.call "clearLimbs" args)
      (.vals [] (clearWordsState st1 ptr n.toNat)) :=
  eval_clearLimbs ptr n lookup_clearLimbs hargs

/-- Lookup-specialized contract for calls from the verified MODEXP program. -/
theorem eval_copyLimbs_verified {V : VEnv D} {st st1 : EvmState}
    {args : List (Expr Op)} (dst src n : U256)
    (hargs : EvalArgs D verifiedFunctions V st args (.vals [dst, src, n] st1)) :
    EvalExpr D verifiedFunctions V st (.call "copyLimbs" args)
      (.vals [] (copyWordsState st1 dst src n.toNat)) :=
  eval_copyLimbs dst src n lookup_copyLimbs hargs

end Challenge.Modexp.Reference.Proofs.Yul.Procedures
