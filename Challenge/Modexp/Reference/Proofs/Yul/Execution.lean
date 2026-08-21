import Challenge.Modexp.Reference.Proofs.Yul.Word
import Challenge.Modexp.Reference.Proofs.Yul.WordMath
import Challenge.YulProof.Interpreter

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Direct execution of the MODEXP Yul dispatcher

This module executes the top-level source block after the independently proved
word and big procedure contracts.  Header decoding, the EIP-7823 size guard,
offset calculation, and branch dispatch are all judgments of the relational
Yul semantics; no compiled-EVM execution theorem is used here.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.Execution

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open Challenge.YulProof.Interpreter
open Challenge.Modexp.Reference.Proofs.Yul
open Challenge.Modexp.Reference.Proofs.Yul.StateModel
open Challenge.Modexp.Reference.Proofs.Yul.WordMath

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

private def headerEnv (input : ByteArray) : VEnv D :=
  [("modulusSize", BitVec.ofNat 256 (modulusSize input)),
    ("esize", BitVec.ofNat 256 (exponentSize input)),
    ("bsize", BitVec.ofNat 256 (baseSize input))]

private def offsetsEnv (input : ByteArray) : VEnv D :=
  [("modOff", BitVec.ofNat 256 (96 + baseSize input + exponentSize input)),
    ("expOff", BitVec.ofNat 256 (96 + baseSize input)),
    ("baseOff", (96 : U256))] ++ headerEnv input

private def emptyReturnedState (st : EvmState) : EvmState :=
  { touchMemory st 0 0 with halted := some (.ret, []) }

private def wordCallAccumulator (st : EvmState) (input : ByteArray) : U256 :=
  let modulus := wordModulus st (BitVec.ofNat 256 (modulusSize input))
    (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))
  let base := basePrefix st (BitVec.ofNat 256 96) modulus
    (BitVec.ofNat 256 (baseSize input)).toNat
  exponentPrefix st (BitVec.ofNat 256 (96 + baseSize input)) base modulus
    (BitVec.ofNat 256 (exponentSize input)).toNat (initialAccumulator modulus)

private theorem size_lt_word {n : Nat} (h : n ≤ 1024) : n < 2 ^ 256 := by
  omega

private theorem headerSize_lt_word (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  norm_num at h ⊢
  exact h

private theorem headerWord_base (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) :
    wordFrom st.env.calldata 0 = BitVec.ofNat 256 (baseSize input) := by
  apply BitVec.eq_of_toNat_eq
  rw [hcd, WordMath.wordFrom_toNat]
  change Precompile.bytesToNatPadded input 0 32 =
    Precompile.bytesToNatPadded input 0 32 % 2 ^ 256
  rw [Nat.mod_eq_of_lt (headerSize_lt_word input 0)]

private theorem headerWord_exponent (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) :
    wordFrom st.env.calldata 32 = BitVec.ofNat 256 (exponentSize input) := by
  apply BitVec.eq_of_toNat_eq
  rw [hcd, WordMath.wordFrom_toNat]
  change Precompile.bytesToNatPadded input 32 32 =
    Precompile.bytesToNatPadded input 32 32 % 2 ^ 256
  rw [Nat.mod_eq_of_lt (headerSize_lt_word input 32)]

private theorem headerWord_modulus (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) :
    wordFrom st.env.calldata 64 = BitVec.ofNat 256 (modulusSize input) := by
  apply BitVec.eq_of_toNat_eq
  rw [hcd, WordMath.wordFrom_toNat]
  change Precompile.bytesToNatPadded input 64 32 =
    Precompile.bytesToNatPadded input 64 32 % 2 ^ 256
  rw [Nat.mod_eq_of_lt (headerSize_lt_word input 64)]

private theorem eval_headerBase (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) :
    EvalExpr D verifiedFunctions [] st (yulE% calldataload(0))
      (.vals [BitVec.ofNat 256 (baseSize input)] st) := by
  have h : EvalExpr D verifiedFunctions [] st (yulE% calldataload(0))
      (.vals [wordFrom st.env.calldata 0] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
    rfl
  rw [headerWord_base st input hcd] at h
  exact h

private theorem eval_headerExponent (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) :
    EvalExpr D verifiedFunctions
      [("bsize", BitVec.ofNat 256 (baseSize input))] st
      (yulE% calldataload(32))
      (.vals [BitVec.ofNat 256 (exponentSize input)] st) := by
  have h : EvalExpr D verifiedFunctions
      [("bsize", BitVec.ofNat 256 (baseSize input))] st
      (yulE% calldataload(32)) (.vals [wordFrom st.env.calldata 32] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
    rfl
  rw [headerWord_exponent st input hcd] at h
  exact h

private theorem eval_headerModulus (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) :
    EvalExpr D verifiedFunctions
      [("esize", BitVec.ofNat 256 (exponentSize input)),
        ("bsize", BitVec.ofNat 256 (baseSize input))] st
      (yulE% calldataload(64))
      (.vals [BitVec.ofNat 256 (modulusSize input)] st) := by
  have h : EvalExpr D verifiedFunctions
      [("esize", BitVec.ofNat 256 (exponentSize input)),
        ("bsize", BitVec.ofNat 256 (baseSize input))] st
      (yulE% calldataload(64)) (.vals [wordFrom st.env.calldata 64] st) := by
    apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
    rfl
  rw [headerWord_modulus st input hcd] at h
  exact h

private theorem literal1024_ult_size (n : Nat) (h : n ≤ 1024) :
    (1024 : U256).ult (BitVec.ofNat 256 n) = false := by
  apply Bool.eq_false_iff.mpr
  intro hlt
  rw [BitVec.ult_iff_toNat_lt] at hlt
  have hn : n < 2 ^ 256 := size_lt_word h
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hlt
  omega

private theorem eval_sizeGt (st : EvmState) (V : VEnv D) (name : String)
    (n : Nat) (hget : V.get name = some (BitVec.ofNat 256 n)) (h : n ≤ 1024) :
    EvalExpr D verifiedFunctions V st
      (mkCall "gt" [.var name, .lit (.number 1024)]) (.vals [(0 : U256)] st) := by
  apply Step.builtinOk (D := D)
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hget))
  simp [D, Challenge.YulProof.ClosedEvm.dialect,
    YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
    YulSemantics.EVM.stepOp, YulSemantics.EVM.bin, YulSemantics.EVM.b2w,
    YulSemantics.EVM.litValue]
  change (if (1024 : U256).ult (BitVec.ofNat 256 n) = true then
    (1 : U256) else 0) = 0
  rw [literal1024_ult_size n h]
  rfl

private theorem eval_sizeGuard (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) :
    EvalExpr D verifiedFunctions (headerEnv input) st
      (yulE% or(or(gt(bsize, 1024), gt(esize, 1024)), gt(modulusSize, 1024)))
      (.vals [(0 : U256)] st) := by
  have hb := eval_sizeGt st (headerEnv input) "bsize" (baseSize input)
    (by rfl) hvalid.2.1
  have he := eval_sizeGt st (headerEnv input) "esize" (exponentSize input)
    (by rfl) hvalid.2.2.1
  have hm := eval_sizeGt st (headerEnv input) "modulusSize" (modulusSize input)
    (by rfl) hvalid.2.2.2
  have hinner : EvalExpr D verifiedFunctions (headerEnv input) st
      (yulE% or(gt(bsize, 1024), gt(esize, 1024))) (.vals [(0 : U256)] st) := by
    apply Step.builtinOk (D := D) (Step.argsCons (Step.argsCons Step.argsNil he) hb)
    rfl
  apply Step.builtinOk (D := D) (Step.argsCons (Step.argsCons Step.argsNil hm) hinner)
  rfl

private theorem exec_sizeGuard (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) :
    ExecStmt D verifiedFunctions (headerEnv input) st
      (.cond
        (yulE% or(or(gt(bsize, 1024), gt(esize, 1024)), gt(modulusSize, 1024)))
        (yul% { invalid() }))
      (headerEnv input) st .normal :=
  Step.ifFalse (D := D) (eval_sizeGuard st input hvalid) rfl

private theorem exec_zeroSizeReturn (st : EvmState) (input : ByteArray)
    (hzero : modulusSize input = 0) :
    ExecStmt D verifiedFunctions (headerEnv input) st
      (.cond (yulE% iszero(modulusSize)) (yul% { return(0, 0) }))
      (headerEnv input) (emptyReturnedState st) .halt := by
  have hcond : EvalExpr D verifiedFunctions (headerEnv input) st
      (yulE% iszero(modulusSize)) (.vals [(1 : U256)] st) := by
    apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil (Step.var (by rfl)))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un, YulSemantics.EVM.b2w,
      headerEnv, hzero]
  have hret : ExecStmt D verifiedFunctions (headerEnv input) st
      (.block (yul% { return(0, 0) })) (headerEnv input)
      (emptyReturnedState st) .halt := by
    refine Step.block (D := D) (Vb := headerEnv input) ?_
    refine Step.seqStop (D := D) (o := .halt) ?_ (by decide)
    refine Step.exprStmtHalt (D := D) ?_
    apply Step.builtinHalt (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit)
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.litValue,
      YulSemantics.EVM.readBytes, emptyReturnedState]
  exact Step.ifTrue (D := D) hcond (by decide) hret

/-- Direct execution of the top-level zero-output-size branch. -/
theorem run_verifiedProgram_zeroSize (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hzero : modulusSize input = 0) :
    Run D verifiedProgram st [] (emptyReturnedState st) .halt := by
  show ExecStmt D [] [] st (.block verifiedProgram) [] (emptyReturnedState st) .halt
  simp only [verifiedProgram]
  refine Step.block (D := D) (Vb := headerEnv input) ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons (Step.letVal (eval_headerBase st input hcd) rfl) ?_
  refine Step.seqCons (Step.letVal (eval_headerExponent st input hcd) rfl) ?_
  refine Step.seqCons (Step.letVal (eval_headerModulus st input hcd) rfl) ?_
  refine Step.seqCons (exec_sizeGuard st input hvalid) ?_
  exact Step.seqStop (exec_zeroSizeReturn st input hzero) (by decide)

private theorem ofNat_size_ne_zero (input : ByteArray) (hpos : 0 < modulusSize input) :
    BitVec.ofNat 256 (modulusSize input) ≠ 0 := by
  intro hzero
  have hnat := congrArg BitVec.toNat hzero
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa [modulusSize] using headerSize_lt_word input 64)] at hnat
  simp at hnat
  omega

private theorem exec_positiveSize (st : EvmState) (input : ByteArray)
    (hpos : 0 < modulusSize input) :
    ExecStmt D verifiedFunctions (headerEnv input) st
      (.cond (yulE% iszero(modulusSize)) (yul% { return(0, 0) }))
      (headerEnv input) st .normal := by
  have hcond : EvalExpr D verifiedFunctions (headerEnv input) st
      (yulE% iszero(modulusSize)) (.vals [(0 : U256)] st) := by
    apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil (Step.var (by rfl)))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un, YulSemantics.EVM.b2w,
      headerEnv]
    exact ofNat_size_ne_zero input hpos
  exact Step.ifFalse (D := D) hcond rfl

private theorem exec_offsets (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) :
    ExecStmts D verifiedFunctions (headerEnv input) st
      [Stmt.letDecl ["baseOff"] (some (yulE% 96)),
        Stmt.letDecl ["expOff"] (some (yulE% add(baseOff, bsize))),
        Stmt.letDecl ["modOff"] (some (yulE% add(expOff, esize)))]
      (offsetsEnv input) st .normal := by
  let offsetStmts : Block Op :=
    [Stmt.letDecl ["baseOff"] (some (yulE% 96)),
      Stmt.letDecl ["expOff"] (some (yulE% add(baseOff, bsize))),
      Stmt.letDecl ["modOff"] (some (yulE% add(expOff, esize)))]
  have hb := hvalid.2.1
  have he := hvalid.2.2.1
  have hbaseAdd : (96 : U256) + BitVec.ofNat 256 (baseSize input) =
      BitVec.ofNat 256 (96 + baseSize input) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (size_lt_word hb),
      Nat.mod_eq_of_lt (by omega : 96 + baseSize input < 2 ^ 256)]
  have hmodAdd : BitVec.ofNat 256 (96 + baseSize input) +
      BitVec.ofNat 256 (exponentSize input) =
      BitVec.ofNat 256 (96 + baseSize input + exponentSize input) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (size_lt_word he),
      Nat.mod_eq_of_lt (by omega : 96 + baseSize input < 2 ^ 256),
      Nat.mod_eq_of_lt
        (by omega : 96 + baseSize input + exponentSize input < 2 ^ 256)]
  have hexp : EvalExpr D verifiedFunctions
      (("baseOff", (96 : U256)) :: headerEnv input) st
      (yulE% add(baseOff, bsize))
      (.vals [BitVec.ofNat 256 (96 + baseSize input)] st) := by
    have hraw : EvalExpr D verifiedFunctions
        (("baseOff", (96 : U256)) :: headerEnv input) st
        (yulE% add(baseOff, bsize))
        (.vals [(96 : U256) + BitVec.ofNat 256 (baseSize input)] st) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
      rfl
    rw [hbaseAdd] at hraw
    exact hraw
  have hmod : EvalExpr D verifiedFunctions
      (("expOff", BitVec.ofNat 256 (96 + baseSize input)) ::
        ("baseOff", (96 : U256)) :: headerEnv input) st
      (yulE% add(expOff, esize))
      (.vals [BitVec.ofNat 256 (96 + baseSize input + exponentSize input)] st) := by
    have hraw : EvalExpr D verifiedFunctions
        (("expOff", BitVec.ofNat 256 (96 + baseSize input)) ::
          ("baseOff", (96 : U256)) :: headerEnv input) st
        (yulE% add(expOff, esize))
        (.vals [BitVec.ofNat 256 (96 + baseSize input) +
          BitVec.ofNat 256 (exponentSize input)] st) := by
      apply evalExpr_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 20)
      rfl
    rw [hmodAdd] at hraw
    exact hraw
  change ExecStmts D verifiedFunctions (headerEnv input) st offsetStmts
    (offsetsEnv input) st .normal
  refine Step.seqCons (D := D) (Step.letVal Step.lit rfl) ?_
  refine Step.seqCons (D := D) (Step.letVal hexp rfl) ?_
  refine Step.seqCons (D := D) (Step.letVal hmod rfl) ?_
  simpa [offsetStmts, offsetsEnv, D, Challenge.YulProof.ClosedEvm.dialect,
    YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.litValue] using (Step.seqNil (D := D)
    (funs := verifiedFunctions) (V := offsetsEnv input) (st := st))

private theorem literal32_ult_size (n : Nat) (h : n ≤ 32) :
    (32 : U256).ult (BitVec.ofNat 256 n) = false := by
  apply Bool.eq_false_iff.mpr
  intro hlt
  rw [BitVec.ult_iff_toNat_lt] at hlt
  have hn : n < 2 ^ 256 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hlt
  omega

private theorem eval_wordCondition (st : EvmState) (input : ByteArray)
    (hword : modulusSize input ≤ 32) :
    EvalExpr D verifiedFunctions (offsetsEnv input) st
      (yulE% iszero(gt(modulusSize, 32))) (.vals [(1 : U256)] st) := by
  have hgt : EvalExpr D verifiedFunctions (offsetsEnv input) st
      (yulE% gt(modulusSize, 32)) (.vals [(0 : U256)] st) := by
    apply Step.builtinOk (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var (by rfl)))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin, YulSemantics.EVM.b2w,
      YulSemantics.EVM.litValue]
    change (if (32 : U256).ult (BitVec.ofNat 256 (modulusSize input)) = true then
      (1 : U256) else 0) = 0
    rw [literal32_ult_size (modulusSize input) hword]
    rfl
  apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil hgt)
  rfl

private theorem eval_wordArgs {funs : FunEnv D} (st : EvmState) (input : ByteArray) :
    EvalArgs D funs (offsetsEnv input) st
      [yulE% bsize, yulE% esize, yulE% modulusSize,
        yulE% baseOff, yulE% expOff, yulE% modOff]
      (.vals [BitVec.ofNat 256 (baseSize input),
        BitVec.ofNat 256 (exponentSize input),
        BitVec.ofNat 256 (modulusSize input), (96 : U256),
        BitVec.ofNat 256 (96 + baseSize input),
        BitVec.ofNat 256 (96 + baseSize input + exponentSize input)] st) := by
  apply evalArgs_of_interp Challenge.YulProof.ClosedEvm.exec_lawful (fuel := 50)
  rfl

private theorem exec_wordCall_zero (st : EvmState) (input : ByteArray)
    (hword : modulusSize input ≤ 32)
    (hzero : sourceModulus st input = 0) :
    ExecStmt D verifiedFunctions (offsetsEnv input) st
      (.cond (yulE% iszero(gt(modulusSize, 32)))
        (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }))
      (offsetsEnv input)
      (zeroModulusReturnedState st (BitVec.ofNat 256 (modulusSize input))) .halt := by
  let callBlock : Block Op := yul% {
    modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff)
  }
  let callFuns : FunEnv D := hoist D callBlock :: verifiedFunctions
  have hcall := eval_modexpWord_zero
    (BitVec.ofNat 256 (baseSize input))
    (BitVec.ofNat 256 (exponentSize input))
    (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
    (BitVec.ofNat 256 (96 + baseSize input))
    (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))
    (funs := callFuns) (V := offsetsEnv input) (st := st) (st1 := st)
    (args := [yulE% bsize, yulE% esize, yulE% modulusSize,
      yulE% baseOff, yulE% expOff, yulE% modOff])
    (by rfl) (by simpa [callFuns, callBlock, hoist] using eval_wordArgs st input)
    (by simpa [sourceModulus, modulusOffset, expOffset, Nat.add_assoc] using hzero)
  have hbody : ExecStmt D verifiedFunctions (offsetsEnv input) st
      (.block callBlock) (offsetsEnv input)
      (zeroModulusReturnedState st (BitVec.ofNat 256 (modulusSize input))) .halt :=
    Step.block (D := D) (Step.seqStop (Step.exprStmtHalt hcall) (by decide))
  simpa [callBlock] using
    (Step.ifTrue (D := D) (eval_wordCondition st input hword) (by decide) hbody)

private theorem exec_wordCall_nonzero (st : EvmState) (input : ByteArray)
    (hword : modulusSize input ≤ 32)
    (hnonzero : sourceModulus st input ≠ 0) :
    ExecStmt D verifiedFunctions (offsetsEnv input) st
      (.cond (yulE% iszero(gt(modulusSize, 32)))
        (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }))
      (offsetsEnv input)
      (wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
        (sourceWordResult st input)) .halt := by
  let callBlock : Block Op := yul% {
    modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff)
  }
  let callFuns : FunEnv D := hoist D callBlock :: verifiedFunctions
  have hcall := eval_modexpWord_nonzero
    (BitVec.ofNat 256 (baseSize input))
    (BitVec.ofNat 256 (exponentSize input))
    (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
    (BitVec.ofNat 256 (96 + baseSize input))
    (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))
    (funs := callFuns) (V := offsetsEnv input) (st := st) (st1 := st)
    (args := [yulE% bsize, yulE% esize, yulE% modulusSize,
      yulE% baseOff, yulE% expOff, yulE% modOff])
    (by rfl) (by simpa [callFuns, callBlock, hoist] using eval_wordArgs st input)
    (by simpa [sourceModulus, modulusOffset, expOffset, Nat.add_assoc] using hnonzero)
  have hbody : ExecStmt D verifiedFunctions (offsetsEnv input) st
      (.block callBlock) (offsetsEnv input)
      (wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
        (sourceWordResult st input)) .halt :=
    by
      have hb : (BitVec.ofNat 256 (baseSize input)).toNat = baseSize input := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          simpa [baseSize] using headerSize_lt_word input 0)]
      have he : (BitVec.ofNat 256 (exponentSize input)).toNat = exponentSize input := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          simpa [exponentSize] using headerSize_lt_word input 32)]
      have hacc : wordCallAccumulator st input = sourceWordResult st input := by
        simp only [wordCallAccumulator, sourceWordResult, sourceBase, sourceModulus,
          modulusOffset, expOffset, Nat.add_assoc, hb, he]
      have hbodyCall : ExecStmt D verifiedFunctions (offsetsEnv input) st
          (.block callBlock) (offsetsEnv input)
          (wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
            (wordCallAccumulator st input)) .halt :=
        Step.block (D := D) (Step.seqStop (Step.exprStmtHalt hcall) (by decide))
      rw [hacc] at hbodyCall
      exact hbodyCall
  simpa [callBlock] using
    (Step.ifTrue (D := D) (eval_wordCondition st input hword) (by decide) hbody)

private theorem execStmts_append_normal {funs : FunEnv D} {V V1 V2 : VEnv D}
    {st st1 st2 : EvmState} {prelude suffix : Block Op} {outcome : Outcome}
    (hprefix : ExecStmts D funs V st prelude V1 st1 .normal)
    (hsuffix : ExecStmts D funs V1 st1 suffix V2 st2 outcome) :
    ExecStmts D funs V st (prelude ++ suffix) V2 st2 outcome := by
  induction prelude generalizing V st with
  | nil =>
      cases hprefix
      simpa using hsuffix
  | cons head rest ih =>
      cases hprefix with
      | seqCons hhead hrest => exact Step.seqCons hhead (ih hrest)
      | seqStop _ hne => exact (hne rfl).elim

private theorem exec_wordTail_zero (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32)
    (hzero : sourceModulus st input = 0) :
    ExecStmts D verifiedFunctions (headerEnv input) st
      [Stmt.letDecl ["baseOff"] (some (yulE% 96)),
        Stmt.letDecl ["expOff"] (some (yulE% add(baseOff, bsize))),
        Stmt.letDecl ["modOff"] (some (yulE% add(expOff, esize))),
        Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (zeroModulusReturnedState st (BitVec.ofNat 256 (modulusSize input))) .halt := by
  have hsuffix : ExecStmts D verifiedFunctions (offsetsEnv input) st
      [Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (zeroModulusReturnedState st (BitVec.ofNat 256 (modulusSize input))) .halt :=
    Step.seqStop (exec_wordCall_zero st input hword hzero) (by decide)
  simpa using execStmts_append_normal (exec_offsets st input hvalid) hsuffix

private theorem exec_wordTail_nonzero (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32)
    (hnonzero : sourceModulus st input ≠ 0) :
    ExecStmts D verifiedFunctions (headerEnv input) st
      [Stmt.letDecl ["baseOff"] (some (yulE% 96)),
        Stmt.letDecl ["expOff"] (some (yulE% add(baseOff, bsize))),
        Stmt.letDecl ["modOff"] (some (yulE% add(expOff, esize))),
        Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
        (sourceWordResult st input)) .halt := by
  have hsuffix : ExecStmts D verifiedFunctions (offsetsEnv input) st
      [Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
        (sourceWordResult st input)) .halt :=
    Step.seqStop (exec_wordCall_nonzero st input hword hnonzero) (by decide)
  simpa using execStmts_append_normal (exec_offsets st input hvalid) hsuffix

private theorem run_prefix_then {st final : EvmState} (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hpos : 0 < modulusSize input)
    (htail : ExecStmts D verifiedFunctions (headerEnv input) st
      [Stmt.letDecl ["baseOff"] (some (yulE% 96)),
        Stmt.letDecl ["expOff"] (some (yulE% add(baseOff, bsize))),
        Stmt.letDecl ["modOff"] (some (yulE% add(expOff, esize))),
        Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input) final .halt) :
    Run D verifiedProgram st [] final .halt := by
  show ExecStmt D [] [] st (.block verifiedProgram) [] final .halt
  simp only [verifiedProgram]
  refine Step.block (D := D) (Vb := offsetsEnv input) ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons Step.funDef ?_
  refine Step.seqCons (Step.letVal (eval_headerBase st input hcd) rfl) ?_
  refine Step.seqCons (Step.letVal (eval_headerExponent st input hcd) rfl) ?_
  refine Step.seqCons (Step.letVal (eval_headerModulus st input hcd) rfl) ?_
  refine Step.seqCons (exec_sizeGuard st input hvalid) ?_
  refine Step.seqCons (exec_positiveSize st input hpos) ?_
  exact htail

/-- Direct execution of the word branch when the decoded modulus is zero. -/
theorem run_verifiedProgram_word_zero (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hpos : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hzero : sourceModulus st input = 0) :
    Run D verifiedProgram st []
      (zeroModulusReturnedState st (BitVec.ofNat 256 (modulusSize input))) .halt :=
  run_prefix_then input hcd hvalid hpos (exec_wordTail_zero st input hvalid hword hzero)

/-- Direct execution of the complete nonzero-modulus word branch. -/
theorem run_verifiedProgram_word_nonzero (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hpos : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hnonzero : sourceModulus st input ≠ 0) :
    Run D verifiedProgram st []
      (wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
        (sourceWordResult st input)) .halt :=
  run_prefix_then input hcd hvalid hpos
    (exec_wordTail_nonzero st input hvalid hword hnonzero)

theorem emptyReturnedState_result (st : EvmState) (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (emptyReturnedState st).halted = some (HaltKind.ret, (spec input).toList) := by
  simp [emptyReturnedState, spec, hzero]

theorem sourceModulus_zero_of_modulusNat_zero (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hword : modulusSize input ≤ 32) (hzero : modulusNat input = 0) :
    sourceModulus st input = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [sourceModulus_toNat st input hcd hvalid hword, hzero]
  rfl

private theorem natToBE_zero (width : Nat) :
    YulEvmCompiler.natToBE 0 width = List.replicate width 0 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [YulEvmCompiler.natToBE, ih]
      change List.replicate width 0 ++ List.replicate 1 0 =
        List.replicate (width + 1) 0
      rw [← List.replicate_add]

theorem zeroModulusReturnedState_result (st : EvmState) (input : ByteArray)
    (hmem : st.memory = fun _ => 0) (hpos : 0 < modulusSize input)
    (hzero : modulusNat input = 0) :
    (zeroModulusReturnedState st (BitVec.ofNat 256 (modulusSize input))).halted =
      some (HaltKind.ret, (spec input).toList) := by
  have hm : (BitVec.ofNat 256 (modulusSize input)).toNat = modulusSize input := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      simpa [modulusSize] using headerSize_lt_word input 64)]
  change some (HaltKind.ret, readBytes st.memory 0x1800
    (BitVec.ofNat 256 (modulusSize input)).toNat) = _
  rw [hm, hmem]
  simp [readBytes, spec, Nat.ne_of_gt hpos, modulusNat] at hzero ⊢
  simp [modulusOffset, expOffset, Nat.add_assoc] at hzero
  rw [← Nat.add_assoc] at hzero
  rw [hzero]
  rw [show Precompile.modPow
      (Precompile.bytesToNatPadded input 96 (baseSize input))
      (Precompile.bytesToNatPadded input (96 + baseSize input) (exponentSize input)) 0 = 0
    by simp [Precompile.modPow]]
  rw [Precompile.natToBytes,
    Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE, natToBE_zero]
  rw [YulEvmCompiler.ByteArray.toList_eq_data]

end Challenge.Modexp.Reference.Proofs.Yul.Execution
