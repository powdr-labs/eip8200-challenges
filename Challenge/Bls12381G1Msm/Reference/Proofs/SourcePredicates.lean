import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePredicateDefs
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGeValue

set_option warningAsError true

/-! Executable and lawful-limb semantics of the frozen field predicates. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

def fpValidValue (hi lo : U256) : U256 :=
  b2w (fpGeModulusValue hi lo = 0)

def fpZeroValue (hi lo : U256) : U256 :=
  b2w (hi = 0) &&& b2w (lo = 0)

def fpEqValue (ahi alo bhi blo : U256) : U256 :=
  b2w (ahi = bhi) &&& b2w (alo = blo)

theorem conv_fpValidValue (hi lo : U256) :
    YulEvmCompiler.conv (fpValidValue hi lo) =
    UInt256.isZero
      (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }) := by
  unfold fpValidValue
  rw [YulEvmCompiler.conv_iszero, conv_fpGeModulusValue]

theorem conv_fpZeroValue (hi lo : U256) :
    YulEvmCompiler.conv (fpZeroValue hi lo) =
    UInt256.land (UInt256.isZero (YulEvmCompiler.conv hi))
      (UInt256.isZero (YulEvmCompiler.conv lo)) := by
  unfold fpZeroValue
  rw [YulEvmCompiler.conv_and, YulEvmCompiler.conv_iszero,
    YulEvmCompiler.conv_iszero]

theorem conv_fpEqValue (ahi alo bhi blo : U256) :
    YulEvmCompiler.conv (fpEqValue ahi alo bhi blo) =
    UInt256.land (UInt256.eq (YulEvmCompiler.conv ahi) (YulEvmCompiler.conv bhi))
      (UInt256.eq (YulEvmCompiler.conv alo) (YulEvmCompiler.conv blo)) := by
  unfold fpEqValue
  rw [YulEvmCompiler.conv_and, YulEvmCompiler.conv_eq,
    YulEvmCompiler.conv_eq]

theorem eval_fpZero (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 sourceFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x002" [.var "hi", .var "lo"]) =
    .ok (.vals [fpZeroValue hi lo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookup_fpZero, fpZeroDecl, fpZeroBody_eq, fpZeroStmt,
    modexpExec, modexpBuiltinFn, stepOp, bin, un, fpZeroValue,
    Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set, bindZeros, restore]

theorem eval_fpEq (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x003" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [fpEqValue ahi alo bhi blo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookup_fpEq, fpEqDecl, fpEqBody_eq, fpEqStmt,
    modexpExec, modexpBuiltinFn, stepOp, bin, fpEqValue,
    Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set, bindZeros, restore]

/-- Relational call boundary for `fpZero`, preserving the state produced by
its (possibly effectful) argument evaluation. -/
theorem step_fpZero_of_args {funs V st argState args} (hi lo : U256)
    (hargs : EvalArgs modexpExec.toDialect funs V st args
      (.vals [hi, lo] argState))
    (hlookup : lookupFun funs "\x002" = some (fpZeroDecl, sourceFuns)) :
    EvalExpr modexpExec.toDialect funs V st (.call "\x002" args)
      (.vals [fpZeroValue hi lo] argState) := by
  let initial : VEnv modexpExec.toDialect :=
    [("\x0026", hi), ("\x0027", lo), ("\x0028", 0)]
  let final : VEnv modexpExec.toDialect :=
    [("\x0026", hi), ("\x0027", lo), ("\x0028", fpZeroValue hi lo)]
  have hlo : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.var "\x0027") (.vals [lo] argState) := Step.var rfl
  have hzlo : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.builtin .iszero [.var "\x0027"])
      (.vals [b2w (lo = 0)] argState) :=
    Step.builtinOk (Step.argsCons Step.argsNil hlo) rfl
  have hhi : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.var "\x0026") (.vals [hi] argState) := Step.var rfl
  have hzhi : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.builtin .iszero [.var "\x0026"])
      (.vals [b2w (hi = 0)] argState) :=
    Step.builtinOk (Step.argsCons Step.argsNil hhi) rfl
  have hand : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.builtin .and
        [.builtin .iszero [.var "\x0026"],
          .builtin .iszero [.var "\x0027"]])
      (.vals [fpZeroValue hi lo] argState) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hzlo) hzhi) rfl
  have hstmt : ExecStmt modexpExec.toDialect ([] :: sourceFuns) initial argState
      fpZeroStmt final argState .normal := by
    rw [fpZeroStmt]
    exact Step.assignVal hand rfl
  have hseq : ExecStmts modexpExec.toDialect ([] :: sourceFuns) initial argState
      fpZeroBody final argState .normal := by
    rw [fpZeroBody_eq]
    exact Step.seqCons hstmt Step.seqNil
  have hblock : ExecStmt modexpExec.toDialect sourceFuns initial argState
      (.block fpZeroBody) (restore initial final) argState .normal := Step.block hseq
  have hcall := Step.callOk hargs hlookup rfl hblock (Or.inl rfl)
  simpa [fpZeroDecl, initial, final, fpZeroValue, Dialect.zero, litValue,
    bindZeros, VEnv.setMany, VEnv.set, VEnv.get, restore] using hcall

/-- Relational call boundary for `fpEq`.  The argument evaluation may touch
memory; the field predicate itself is pure and preserves that resulting state. -/
theorem step_fpEq_of_args {funs V st argState args}
    (ahi alo bhi blo : U256)
    (hargs : EvalArgs modexpExec.toDialect funs V st args
      (.vals [ahi, alo, bhi, blo] argState))
    (hlookup : lookupFun funs "\x003" = some (fpEqDecl, sourceFuns)) :
    EvalExpr modexpExec.toDialect funs V st (.call "\x003" args)
      (.vals [fpEqValue ahi alo bhi blo] argState) := by
  let initial : VEnv modexpExec.toDialect :=
    [("\x0029", ahi), ("\x0030", alo), ("\x0031", bhi), ("\x0032", blo),
      ("\x0033", 0)]
  let final : VEnv modexpExec.toDialect :=
    [("\x0029", ahi), ("\x0030", alo), ("\x0031", bhi), ("\x0032", blo),
      ("\x0033", fpEqValue ahi alo bhi blo)]
  have hbhi : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.var "\x0031") (.vals [bhi] argState) := Step.var rfl
  have hahi : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.var "\x0029") (.vals [ahi] argState) := Step.var rfl
  have heqHi : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.builtin .eq [.var "\x0029", .var "\x0031"])
      (.vals [b2w (ahi = bhi)] argState) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hbhi) hahi) rfl
  have hblo : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.var "\x0032") (.vals [blo] argState) := Step.var rfl
  have halo : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.var "\x0030") (.vals [alo] argState) := Step.var rfl
  have heqLo : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.builtin .eq [.var "\x0030", .var "\x0032"])
      (.vals [b2w (alo = blo)] argState) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil hblo) halo) rfl
  have hand : EvalExpr modexpExec.toDialect ([] :: sourceFuns) initial argState
      (.builtin .and
        [.builtin .eq [.var "\x0029", .var "\x0031"],
          .builtin .eq [.var "\x0030", .var "\x0032"]])
      (.vals [fpEqValue ahi alo bhi blo] argState) :=
    Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil heqLo) heqHi) rfl
  have hstmt : ExecStmt modexpExec.toDialect ([] :: sourceFuns) initial argState
      fpEqStmt final argState .normal := by
    rw [fpEqStmt]
    exact Step.assignVal hand rfl
  have hseq : ExecStmts modexpExec.toDialect ([] :: sourceFuns) initial argState
      fpEqBody final argState .normal := by
    rw [fpEqBody_eq]
    exact Step.seqCons hstmt Step.seqNil
  have hblock : ExecStmt modexpExec.toDialect sourceFuns initial argState
      (.block fpEqBody) (restore initial final) argState .normal := Step.block hseq
  have hcall := Step.callOk hargs hlookup rfl hblock (Or.inl rfl)
  simpa [fpEqDecl, initial, final, fpEqValue, Dialect.zero, litValue,
    bindZeros, VEnv.setMany, VEnv.set, VEnv.get, restore] using hcall

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
