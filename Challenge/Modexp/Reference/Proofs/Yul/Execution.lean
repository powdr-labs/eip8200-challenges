import Challenge.Modexp.Reference.Proofs.Yul.Word
import Challenge.Modexp.Reference.Proofs.Yul.WordMath
import Challenge.Modexp.Reference.Proofs.Yul.BigPath
import Challenge.Modexp.Reference.Proofs.Yul.BigFinal
import Challenge.YulProof.Interpreter
import YulEvmCompiler.Optimizer.Implementation.ReuseValuesSound

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

private theorem literal32_ult_size_true (n : Nat) (h : 32 < n) (hlt : n < 2 ^ 256) :
    (32 : U256).ult (BitVec.ofNat 256 n) = true := by
  rw [BitVec.ult_iff_toNat_lt]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact h

private theorem eval_bigCondition (st : EvmState) (input : ByteArray)
    (hbig : 32 < modulusSize input) :
    EvalExpr D verifiedFunctions (offsetsEnv input) st
      (yulE% iszero(gt(modulusSize, 32))) (.vals [(0 : U256)] st) := by
  have hgt : EvalExpr D verifiedFunctions (offsetsEnv input) st
      (yulE% gt(modulusSize, 32)) (.vals [(1 : U256)] st) := by
    apply Step.builtinOk (D := D)
      (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var (by rfl)))
    simp [D, Challenge.YulProof.ClosedEvm.dialect,
      YulSemantics.EVM.evmWithExternal, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin, YulSemantics.EVM.b2w,
      YulSemantics.EVM.litValue]
    change (if (32 : U256).ult (BitVec.ofNat 256 (modulusSize input)) = true then
      (1 : U256) else 0) = 1
    rw [literal32_ult_size_true (modulusSize input) hbig (by
      simpa [modulusSize] using headerSize_lt_word input 64)]
    rfl
  apply Step.builtinOk (D := D) (Step.argsCons Step.argsNil hgt)
  rfl

private theorem exec_bigCall_zero (st : EvmState) (input : ByteArray)
    (hzero : BigPath.modulusOrValue st (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)) = 0) :
    EvalExpr D verifiedFunctions (offsetsEnv input) st
      (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))
      (.halt (BigPath.zeroModulusReturnedState st
        (BitVec.ofNat 256 (modulusSize input))
        (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)))) := by
  apply BigPath.eval_modexpBig_zero
    (BitVec.ofNat 256 (baseSize input))
    (BitVec.ofNat 256 (exponentSize input))
    (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
    (BitVec.ofNat 256 (96 + baseSize input))
    (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))
    (by rfl) (eval_wordArgs st input) hzero

private theorem exec_bigTail_zero (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input)
    (hzero : BigPath.modulusOrValue st (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)) = 0) :
    ExecStmts D verifiedFunctions (headerEnv input) st
      [Stmt.letDecl ["baseOff"] (some (yulE% 96)),
        Stmt.letDecl ["expOff"] (some (yulE% add(baseOff, bsize))),
        Stmt.letDecl ["modOff"] (some (yulE% add(expOff, esize))),
        Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (BigPath.zeroModulusReturnedState st
        (BitVec.ofNat 256 (modulusSize input))
        (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))) .halt := by
  have hwordIf : ExecStmt D verifiedFunctions (offsetsEnv input) st
      (.cond (yulE% iszero(gt(modulusSize, 32)))
        (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }))
      (offsetsEnv input) st .normal :=
    Step.ifFalse (D := D) (eval_bigCondition st input hbig) rfl
  have hsuffix : ExecStmts D verifiedFunctions (offsetsEnv input) st
      [Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (BigPath.zeroModulusReturnedState st
        (BitVec.ofNat 256 (modulusSize input))
        (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))) .halt :=
    Step.seqCons hwordIf
      (Step.seqStop (Step.exprStmtHalt (exec_bigCall_zero st input hzero)) (by decide))
  simpa using execStmts_append_normal (exec_offsets st input hvalid) hsuffix

/-- Direct top-level execution of the big-path zero-modulus return. -/
theorem run_verifiedProgram_big_zero (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hzero : BigPath.modulusOrValue st (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)) = 0) :
    Run D verifiedProgram st []
      (BigPath.zeroModulusReturnedState st
        (BitVec.ofNat 256 (modulusSize input))
        (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))) .halt :=
  run_prefix_then input hcd hvalid (by omega)
    (exec_bigTail_zero st input hvalid hbig hzero)

private theorem exec_bigCall_nonzero (st : EvmState) (input : ByteArray)
    (hnonzero : BigPath.modulusOrValue st
      (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)) ≠ 0) :
    EvalExpr D verifiedFunctions (offsetsEnv input) st
      (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))
      (.halt (BigPath.returnedResultState
        (BigPath.exponentiatedState st
          (BitVec.ofNat 256 (baseSize input))
          (BitVec.ofNat 256 (exponentSize input))
          (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
          (BitVec.ofNat 256 (96 + baseSize input))
          (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)))
        (BitVec.ofNat 256 (modulusSize input)))) := by
  apply BigPath.eval_modexpBig_nonzero_verified
    (BitVec.ofNat 256 (baseSize input))
    (BitVec.ofNat 256 (exponentSize input))
    (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
    (BitVec.ofNat 256 (96 + baseSize input))
    (BitVec.ofNat 256 (96 + baseSize input + exponentSize input))
    (eval_wordArgs st input) hnonzero

private theorem exec_bigTail_nonzero (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input)
    (hnonzero : BigPath.modulusOrValue st
      (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)) ≠ 0) :
    ExecStmts D verifiedFunctions (headerEnv input) st
      [Stmt.letDecl ["baseOff"] (some (yulE% 96)),
        Stmt.letDecl ["expOff"] (some (yulE% add(baseOff, bsize))),
        Stmt.letDecl ["modOff"] (some (yulE% add(expOff, esize))),
        Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (BigPath.returnedResultState
        (BigPath.exponentiatedState st
          (BitVec.ofNat 256 (baseSize input))
          (BitVec.ofNat 256 (exponentSize input))
          (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
          (BitVec.ofNat 256 (96 + baseSize input))
          (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)))
        (BitVec.ofNat 256 (modulusSize input))) .halt := by
  have hwordIf : ExecStmt D verifiedFunctions (offsetsEnv input) st
      (.cond (yulE% iszero(gt(modulusSize, 32)))
        (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }))
      (offsetsEnv input) st .normal :=
    Step.ifFalse (D := D) (eval_bigCondition st input hbig) rfl
  have hsuffix : ExecStmts D verifiedFunctions (offsetsEnv input) st
      [Stmt.cond (yulE% iszero(gt(modulusSize, 32)))
          (yul% { modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) }),
        Stmt.exprStmt
          (yulE% modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff))]
      (offsetsEnv input)
      (BigPath.returnedResultState
        (BigPath.exponentiatedState st
          (BitVec.ofNat 256 (baseSize input))
          (BitVec.ofNat 256 (exponentSize input))
          (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
          (BitVec.ofNat 256 (96 + baseSize input))
          (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)))
        (BitVec.ofNat 256 (modulusSize input))) .halt :=
    Step.seqCons hwordIf
      (Step.seqStop (Step.exprStmtHalt
        (exec_bigCall_nonzero st input hnonzero)) (by decide))
  simpa using execStmts_append_normal (exec_offsets st input hvalid) hsuffix

/-- Direct top-level execution of the nonzero big path. -/
theorem run_verifiedProgram_big_nonzero (st : EvmState) (input : ByteArray)
    (hcd : st.env.calldata = input.toList) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hnonzero : BigPath.modulusOrValue st
      (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)) ≠ 0) :
    Run D verifiedProgram st []
      (BigPath.returnedResultState
        (BigPath.exponentiatedState st
          (BitVec.ofNat 256 (baseSize input))
          (BitVec.ofNat 256 (exponentSize input))
          (BitVec.ofNat 256 (modulusSize input)) (BitVec.ofNat 256 96)
          (BitVec.ofNat 256 (96 + baseSize input))
          (BitVec.ofNat 256 (96 + baseSize input + exponentSize input)))
        (BitVec.ofNat 256 (modulusSize input))) .halt :=
  run_prefix_then input hcd hvalid (by omega)
    (exec_bigTail_nonzero st input hvalid hbig hnonzero)

theorem run_verifiedProgram_big_nonzero_result (st : EvmState)
    (input : ByteArray) (hcd : st.env.calldata = input.toList)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input)
    (hmodulus : BigSetup.modulusNat input ≠ 0) :
    let final := BigPath.returnedResultState
      (BigPath.exponentiatedState st
        (BitVec.ofNat 256 (baseSize input))
        (BitVec.ofNat 256 (exponentSize input))
        (BitVec.ofNat 256 (modulusSize input)) 96
        (BitVec.ofNat 256 (BigFinal.exponentOffset input))
        (BitVec.ofNat 256 (BigSetup.modulusOffset input)))
      (BitVec.ofNat 256 (modulusSize input))
    Run D verifiedProgram st [] final .halt ∧
      final.halted = some (HaltKind.ret, (spec input).toList) := by
  have hsource : BigPath.modulusOrValue st
      (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (BigSetup.modulusOffset input)) ≠ 0 := by
    intro hzero
    exact hmodulus ((BigSetup.modulusOrValue_eq_zero_iff st input hcd hvalid).mp
      hzero)
  constructor
  · simpa [BigFinal.exponentOffset, BigSetup.modulusOffset] using
      run_verifiedProgram_big_nonzero st input hcd hvalid hbig hsource
  · exact BigFinal.returnedResultState_nonzero_spec_complete st input hcd
      hvalid hbig hmodulus

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

private theorem readBytes_zero_of_represents (memory : Nat → UInt8)
    (ptr count width : Nat) (hwidth : width ≤ 32 * count)
    (hrep : BigMath.Represents memory ptr count 0) :
    readBytes memory ptr width = List.replicate width 0 := by
  have hlimbs : BigMath.memoryLimbs memory ptr count =
      List.replicate count 0 :=
    hrep.2.trans (by simp [Limbs.limbDigits, Nat.digitsAppend])
  have hloads : ∀ i (_hi : i < count),
      loadWord memory (ptr + 32 * i) = 0 := by
    intro i hi
    apply BitVec.eq_of_toNat_eq
    have hget := congrArg (fun xs : List Nat => xs[i]?) hlimbs
    simpa [BigMath.memoryLimbs, hi] using hget
  have hfull :=
    YulEvmCompiler.Optimizer.ReuseValues.readBytes_wordsBytes
      (mem := memory) (ws := List.replicate count (0 : U256)) (a := ptr) (by
        intro i hi
        have hi' : i < count := by simpa using hi
        simpa [hi'] using hloads i hi')
  have words_zero : ∀ n : Nat,
      YulEvmCompiler.Optimizer.ReuseValues.wordsBytes
        (List.replicate n (0 : U256)) = List.replicate (32 * n) 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ,
          YulEvmCompiler.Optimizer.ReuseValues.wordsBytes]
        rw [ih]
        rw [show 32 * (n + 1) = 32 + 32 * n by omega,
          List.replicate_add]
        simp [YulEvmCompiler.Optimizer.ReuseValues.wordBytes,
          YulSemantics.EVM.byteAt]
  have hwords := words_zero count
  have hfullzero : readBytes memory ptr (32 * count) =
      List.replicate (32 * count) 0 := by
    simpa using hfull.trans hwords
  have htake := congrArg (List.take width) hfullzero
  unfold readBytes at htake ⊢
  rw [← List.map_take] at htake
  simpa [List.take_range, List.take_replicate,
    Nat.min_eq_left hwidth] using htake

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

theorem bigZeroModulusReturnedState_result (st : EvmState)
    (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hzero : BigSetup.modulusNat input = 0) :
    (BigPath.zeroModulusReturnedState st
      (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (BigSetup.modulusOffset input))).halted =
      some (HaltKind.ret, (spec input).toList) := by
  let m := modulusSize input
  let off := BigSetup.modulusOffset input
  let count := Limbs.limbCount m
  let cleared := BigPath.clearedOutputState st (BitVec.ofNat 256 m)
  let loaded := BigPath.loadedModulusState st (BitVec.ofNat 256 m)
    (BitVec.ofNat 256 off)
  let scanned := BigPath.scannedModulusState st (BitVec.ofNat 256 m)
    (BitVec.ofNat 256 off)
  have hm : m ≤ 1024 := hvalid.2.2.2
  have hcount : count ≤ 32 := Limbs.limbCount_le_32 m hm
  have hn := BigSetup.limbCount_toNat m hm
  have hmWord : (BitVec.ofNat 256 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 2 ^ 256)]
  have hcleared : BigMath.Represents cleared.memory 6144 count 0 := by
    simpa [cleared, BigPath.clearedOutputState, hn] using
      BigMath.clearWordsState_represents_zero
        (BigPath.clearedAccumulatorState st (BitVec.ofNat 256 m)) 6144 count
        (by omega)
  have hloaded : BigMath.Represents loaded.memory 6144 count 0 := by
    have hpreserved := BigSetup.loadBigEndianPrefix_preserves cleared off m 0
      m 6144 count 0 (by omega) (by omega) (by omega) (by left; omega)
      hcleared
    simpa [loaded, BigPath.loadedModulusState, cleared, hmWord] using hpreserved
  have hscanned : BigMath.Represents scanned.memory 6144 count 0 := by
    simpa [scanned, BigPath.scannedModulusState, hn,
      BigSetup.modulusScanPrefix_memory] using hloaded
  have hread : readBytes scanned.memory 6144 m = List.replicate m 0 :=
    readBytes_zero_of_represents scanned.memory 6144 count m
      (Limbs.width_le_limbs m) hscanned
  have hspec : (spec input).toList = List.replicate m 0 := by
    unfold spec
    rw [if_neg (by omega)]
    rw [show Precompile.bytesToNatPadded input
      (96 + baseSize input + exponentSize input) (modulusSize input) =
        BigSetup.modulusNat input by rfl, hzero]
    simp only
    rw [show Precompile.modPow
      (Precompile.bytesToNatPadded input 96 (baseSize input))
      (Precompile.bytesToNatPadded input (96 + baseSize input)
        (exponentSize input)) 0 = 0 by simp [Precompile.modPow]]
    rw [Precompile.natToBytes,
      Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE, natToBE_zero]
    rw [YulEvmCompiler.ByteArray.toList_eq_data]
  change some (HaltKind.ret, readBytes scanned.memory 6144
    (BitVec.ofNat 256 m).toNat) = _
  rw [hmWord, hread, hspec]

/-- Assemble the complete source contract once the nonzero big branch supplies
its exact execution-and-result endpoint.  Keeping this theorem here makes the
remaining dependency explicit while all other top-level cases stay closed. -/
theorem verifiedProgram_computesResult_of_big
    (hbig : ∀ st input, st.memory = (fun _ => 0) →
      st.env.calldata = input.toList → ValidInput input →
      32 < modulusSize input →
      ∃ final, Run D verifiedProgram st [] final .halt ∧
        final.halted = some (HaltKind.ret, (spec input).toList)) :
    ComputesResult verifiedProgram := by
  intro st hpre
  obtain ⟨hmem, _hnotHalted, input, hcd, hvalid⟩ := hpre
  by_cases hsize : modulusSize input = 0
  · refine ⟨[], emptyReturnedState st, .halt,
      run_verifiedProgram_zeroSize st input hcd hvalid hsize, rfl, ?_⟩
    simpa [resultBytes, hcd, YulEvmCompiler.mkCode_toList] using
      emptyReturnedState_result st input hsize
  by_cases hword : modulusSize input ≤ 32
  · have hpos : 0 < modulusSize input := Nat.pos_of_ne_zero hsize
    by_cases hmodulus : modulusNat input = 0
    · have hsource := sourceModulus_zero_of_modulusNat_zero st input hcd hvalid
        hword hmodulus
      refine ⟨[], zeroModulusReturnedState st
          (BitVec.ofNat 256 (modulusSize input)), .halt,
        run_verifiedProgram_word_zero st input hcd hvalid hpos hword hsource,
        rfl, ?_⟩
      simpa [resultBytes, hcd, YulEvmCompiler.mkCode_toList] using
        zeroModulusReturnedState_result st input hmem hpos hmodulus
    · have hsource := sourceModulus_nonzero st input hcd hvalid hword hmodulus
      refine ⟨[], wordReturnedState st (BitVec.ofNat 256 (modulusSize input))
          (sourceWordResult st input), .halt,
        run_verifiedProgram_word_nonzero st input hcd hvalid hpos hword hsource,
        rfl, ?_⟩
      simpa [resultBytes, hcd, YulEvmCompiler.mkCode_toList] using
        wordReturnedState_result st input hmem hcd hvalid hpos hword hmodulus
  · have hlarge : 32 < modulusSize input := by omega
    obtain ⟨final, hrun, hresult⟩ := hbig st input hmem hcd hvalid hlarge
    refine ⟨[], final, .halt, hrun, rfl, ?_⟩
    simpa [resultBytes, hcd, YulEvmCompiler.mkCode_toList] using hresult

/-- The reference MODEXP source returns the specification on every valid
input, proved directly against the relational Yul semantics. -/
theorem verifiedProgram_computesResult : ComputesResult verifiedProgram := by
  apply verifiedProgram_computesResult_of_big
  intro st input _hmem hcd hvalid hbig
  by_cases hmodulus : BigSetup.modulusNat input = 0
  · have hsource : BigPath.modulusOrValue st
        (BitVec.ofNat 256 (modulusSize input))
        (BitVec.ofNat 256 (BigSetup.modulusOffset input)) = 0 :=
      (BigSetup.modulusOrValue_eq_zero_iff st input hcd hvalid).mpr hmodulus
    let final := BigPath.zeroModulusReturnedState st
      (BitVec.ofNat 256 (modulusSize input))
      (BitVec.ofNat 256 (BigSetup.modulusOffset input))
    refine ⟨final, ?_, ?_⟩
    · simpa [final, BigSetup.modulusOffset] using
        run_verifiedProgram_big_zero st input hcd hvalid hbig hsource
    · simpa [final] using
        bigZeroModulusReturnedState_result st input hvalid hbig hmodulus
  · let final := BigPath.returnedResultState
      (BigPath.exponentiatedState st
        (BitVec.ofNat 256 (baseSize input))
        (BitVec.ofNat 256 (exponentSize input))
        (BitVec.ofNat 256 (modulusSize input)) 96
        (BitVec.ofNat 256 (BigFinal.exponentOffset input))
        (BitVec.ofNat 256 (BigSetup.modulusOffset input)))
      (BitVec.ofNat 256 (modulusSize input))
    have hresult := run_verifiedProgram_big_nonzero_result st input hcd hvalid
      hbig hmodulus
    exact ⟨final, hresult.1, hresult.2⟩

end Challenge.Modexp.Reference.Proofs.Yul.Execution
