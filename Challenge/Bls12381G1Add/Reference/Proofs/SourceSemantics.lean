import Challenge.Bls12381G1Add.Reference.Proofs.Compilation
import Challenge.Bls12381.ProofSupport.FpAddSub
import Challenge.EvmProof.ModexpExec

set_option warningAsError true

/-!
# Source semantics of the proof-friendly G1ADD runtime

The proofs in this directory connect the frozen normalized source block to
the local EIP-correct G1 specification.  They use the deterministic MODEXP
sub-interpreter only to construct derivations of the same open relational
dialect consumed by compiler correctness.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof
open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

/-- Source-word form of the high-first BLS modulus comparison. -/
def fpGeModulusValue (hi lo : U256) : U256 :=
  b2w (BitVec.ult
      (BitVec.ofNat 256 34565483545414906068789196026815425751) hi) |||
    (b2w (hi = BitVec.ofNat 256
      34565483545414906068789196026815425751) &&&
      b2w (b2w (BitVec.ult lo
        (BitVec.ofNat 256
          45442060874369865957053122457065728162598490762543039060009208264153100167851)) = 0))

/-- Source-word validity predicate, defined by the frozen source's negation of
the modulus comparison helper. -/
def fpValidValue (hi lo : U256) : U256 :=
  b2w (fpGeModulusValue hi lo = 0)

/-- Source-word zero test over the two decoded field limbs. -/
def fpZeroValue (hi lo : U256) : U256 :=
  b2w (hi = 0) &&& b2w (lo = 0)

/-- Source-word equality test over two pairs of decoded field limbs. -/
def fpEqValue (ahi alo bhi blo : U256) : U256 :=
  b2w (ahi = bhi) &&& b2w (alo = blo)

/-- Exact two-word result of the frozen source's canonical field addition. -/
def fpAddValue (ahi alo bhi blo : U256) : U256 × U256 :=
  let sLo := alo + blo
  let sHi := ahi + bhi + b2w (BitVec.ult sLo alo)
  if fpGeModulusValue sHi sLo = 0 then (sHi, sLo)
  else
    (sHi - (BitVec.ofNat 256 34565483545414906068789196026815425751 +
      b2w (BitVec.ult sLo
        (BitVec.ofNat 256
          45442060874369865957053122457065728162598490762543039060009208264153100167851))),
     sLo - BitVec.ofNat 256
       45442060874369865957053122457065728162598490762543039060009208264153100167851)

/-- The frozen source's initial two-word subtraction. -/
def fpSubRawValue (ahi alo bhi blo : U256) : U256 × U256 :=
  (ahi - bhi - b2w (BitVec.ult alo blo), alo - blo)

/-- The frozen source's high-word underflow test. -/
def fpSubNeedsRepairValue (diff : U256 × U256) : U256 :=
  b2w (BitVec.ult
    (BitVec.ofNat 256 34565483545414906068789196026815425751) diff.1)

/-- The frozen source's conditional modulus-addition repair. -/
def fpSubRepairValue (diff : U256 × U256) : U256 × U256 :=
  let newLo := diff.2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  (diff.1 + BitVec.ofNat 256 34565483545414906068789196026815425751 +
    b2w (BitVec.ult newLo diff.2), newLo)

/-- Exact two-word result of the frozen source's canonical field subtraction. -/
def fpSubValue (ahi alo bhi blo : U256) : U256 × U256 :=
  let diff := fpSubRawValue ahi alo bhi blo
  if fpSubNeedsRepairValue diff = 0 then diff else fpSubRepairValue diff

theorem conv_fpGeModulusValue (hi lo : U256) :
    YulEvmCompiler.conv (fpGeModulusValue hi lo) =
    Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo } := by
  have hhi : YulEvmCompiler.conv (BitVec.ofNat 256
      34565483545414906068789196026815425751) =
      Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  have hlo : YulEvmCompiler.conv (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167851) =
      Challenge.Bls12381.ProofSupport.Fp.modulusLo := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  unfold fpGeModulusValue
  rw [YulEvmCompiler.conv_or, YulEvmCompiler.conv_gt,
    YulEvmCompiler.conv_and, YulEvmCompiler.conv_eq,
    YulEvmCompiler.conv_iszero, YulEvmCompiler.conv_lt, hhi, hlo]
  rfl

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

theorem conv_fpAddValue (ahi alo bhi blo : U256) :
    ({ hi := YulEvmCompiler.conv (fpAddValue ahi alo bhi blo).1,
       lo := YulEvmCompiler.conv (fpAddValue ahi alo bhi blo).2 } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) =
    Challenge.Bls12381.ProofSupport.Fp.addSource
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } := by
  let sLo := alo + blo
  let sHi := ahi + bhi + b2w (BitVec.ult sLo alo)
  let a : Challenge.Bls12381.ProofSupport.Fp.Limbs :=
    { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
  let b : Challenge.Bls12381.ProofSupport.Fp.Limbs :=
    { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }
  have hsum : Challenge.Bls12381.ProofSupport.Fp.addRaw a b =
      { hi := YulEvmCompiler.conv sHi, lo := YulEvmCompiler.conv sLo } := by
    simp [a, b, sHi, sLo, Challenge.Bls12381.ProofSupport.Fp.addRaw,
      YulEvmCompiler.conv_add, YulEvmCompiler.conv_lt]
  have hge : YulEvmCompiler.conv (fpGeModulusValue sHi sLo) =
      Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        (Challenge.Bls12381.ProofSupport.Fp.addRaw a b) := by
    rw [conv_fpGeModulusValue, hsum]
  have hhi : YulEvmCompiler.conv (BitVec.ofNat 256
      34565483545414906068789196026815425751) =
      Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  have hlo : YulEvmCompiler.conv (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167851) =
      Challenge.Bls12381.ProofSupport.Fp.modulusLo := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  by_cases hc : fpGeModulusValue sHi sLo = 0
  · have hkeep : ¬(Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        (Challenge.Bls12381.ProofSupport.Fp.addRaw a b)).toNat ≠ 0 := by
      simp only [not_ne_iff]
      rw [← hge, hc]
      rfl
    unfold fpAddValue Challenge.Bls12381.ProofSupport.Fp.addSource
    rw [if_pos hc, if_neg hkeep, hsum]
  · have hcorrect :
        (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
          (Challenge.Bls12381.ProofSupport.Fp.addRaw a b)).toNat ≠ 0 := by
      intro hzero
      have hnat := congrArg UInt256.toNat hge
      rw [hzero] at hnat
      apply hc
      apply BitVec.toNat_injective
      simpa using hnat
    unfold fpAddValue Challenge.Bls12381.ProofSupport.Fp.addSource
      Challenge.Bls12381.ProofSupport.Fp.addCorrect
    rw [if_neg hc, if_pos hcorrect, hsum]
    repeat rw [YulEvmCompiler.conv_sub]
    repeat rw [YulEvmCompiler.conv_add]
    repeat rw [YulEvmCompiler.conv_lt]
    rw [hhi, hlo]
    rfl

private def isFunctionDefinition {Op : Type} : Stmt Op → Bool
  | .funDef .. => true
  | _ => false

private theorem execStmts_function_prefix
    (E : ExecDialect) [DecidableEq E.toDialect.Value]
    (defs rest : List (Stmt E.toDialect.Op))
    (hdefs : defs.all isFunctionDefinition = true)
    (fuel : Nat) (hfuel : 0 < fuel) (funs V st) :
    Interp.execStmts E (fuel + defs.length) funs V st (defs ++ rest) =
      Interp.execStmts E fuel funs V st rest := by
  induction defs with
  | nil => simp
  | cons head tail ih =>
      have hparts : isFunctionDefinition head = true ∧
          tail.all isFunctionDefinition = true := by
        simpa using hdefs
      cases head <;> simp only [isFunctionDefinition, Bool.false_eq_true] at hparts
      all_goals try { exact False.elim hparts.1 }
      case funDef name params rets body =>
        have hpositive : 0 < fuel + tail.length := by omega
        obtain ⟨k, hk⟩ : ∃ k, fuel + tail.length = k + 1 :=
          ⟨fuel + tail.length - 1, by omega⟩
        rw [show fuel + (Stmt.funDef name params rets body :: tail).length =
          (k + 1) + 1 by simp; omega]
        change Interp.execStmts E (k + 1) funs V st
          (tail ++ rest) = Interp.execStmts E fuel funs V st rest
        rw [← hk]
        exact ih hparts.2

private def invalidLengthStmt : Stmt Op :=
  .cond
    (.builtin .iszero
      [.builtin .eq [.builtin .calldatasize [], .lit (.number 256)]])
    [.exprStmt (.builtin .invalid [])]

private theorem reference_after_functions :
    referenceCompiledBlock.drop 13 =
      invalidLengthStmt :: referenceCompiledBlock.drop 14 := by
  rfl

private theorem reference_function_prefix :
    (referenceCompiledBlock.take 13).all isFunctionDefinition = true := by
  rfl

private theorem reference_function_prefix_length :
    (referenceCompiledBlock.take 13).length = 13 := by
  rfl

private theorem exec_reference_function_prefix (funs V st) :
    Interp.execStmts modexpExec 127 funs V st referenceCompiledBlock =
      Interp.execStmts modexpExec 114 funs V st
        (invalidLengthStmt :: referenceCompiledBlock.drop 14) := by
  have hprefix := execStmts_function_prefix modexpExec
    (referenceCompiledBlock.take 13) (referenceCompiledBlock.drop 13)
    reference_function_prefix 114 (by omega) funs V st
  rw [reference_function_prefix_length] at hprefix
  norm_num at hprefix
  calc
    Interp.execStmts modexpExec 127 funs V st referenceCompiledBlock =
        Interp.execStmts modexpExec 127 funs V st
          (referenceCompiledBlock.take 13 ++ referenceCompiledBlock.drop 13) := by
      rw [List.take_append_drop]
    _ = Interp.execStmts modexpExec 114 funs V st
          (referenceCompiledBlock.drop 13) := hprefix
    _ = Interp.execStmts modexpExec 114 funs V st
          (invalidLengthStmt :: referenceCompiledBlock.drop 14) := by
      rw [reference_after_functions]

/-- The first frozen helper implements the high-first modulus comparison used
by the approved source-faithful Fp schedules. -/
theorem eval_fpGeModulus (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x000" [.var "hi", .var "lo"]) =
    .ok (.vals [fpGeModulusValue hi lo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookupFun, hoist, referenceCompiledBlock, frozenReferenceBlock,
    modexpExec, modexpBuiltinFn, stepOp, bin, un, fpGeModulusValue,
    Dialect.zero, restore]
  rfl

/-- The second frozen helper negates `fpGeModulus` exactly once. -/
theorem eval_fpValid (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [fpValidValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

/-- The third frozen helper tests both decoded limbs for zero. -/
theorem eval_fpZero (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x002" [.var "hi", .var "lo"]) =
    .ok (.vals [fpZeroValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

/-- The fourth frozen helper compares both decoded field limbs. -/
theorem eval_fpEq (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x003" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [fpEqValue ahi alo bhi blo] yst) := by
  rw [Interp.evalExpr]
  rfl

/-- The fifth frozen helper executes the approved source-faithful field-add
schedule and returns its high word before its low word. -/
theorem eval_fpAdd (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x004" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpAddValue ahi alo bhi blo).1,
      (fpAddValue ahi alo bhi blo).2] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookupFun, hoist, referenceCompiledBlock, frozenReferenceBlock,
    modexpExec, modexpBuiltinFn, stepOp, bin, un,
    Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set,
    bindZeros, restore]
  split
  case isTrue hsource =>
    have hnamed := hsource
    change fpGeModulusValue
      (ahi + bhi + b2w (BitVec.ult (alo + blo) alo)) (alo + blo) = 0 at hnamed
    simp [fpAddValue, hnamed]
  case isFalse hsource =>
    have hnamed := hsource
    change ¬fpGeModulusValue
      (ahi + bhi + b2w (BitVec.ult (alo + blo) alo)) (alo + blo) = 0 at hnamed
    unfold fpAddValue
    rw [if_neg hnamed]
    rfl

/-- The sixth frozen helper executes the approved source-faithful field-sub
schedule and returns its high word before its low word. -/
theorem eval_fpSub (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x005" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fpSubValue ahi alo bhi blo).1,
      (fpSubValue ahi alo bhi blo).2] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookupFun, hoist, referenceCompiledBlock, frozenReferenceBlock,
    modexpExec, modexpBuiltinFn, stepOp, bin,
    Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set,
    bindZeros, restore]
  split
  case isTrue hsource =>
    have hnamed := hsource
    change fpSubNeedsRepairValue (fpSubRawValue ahi alo bhi blo) = 0 at hnamed
    unfold fpSubValue
    rw [if_pos hnamed]
    rfl
  case isFalse hsource =>
    have hnamed := hsource
    change ¬fpSubNeedsRepairValue (fpSubRawValue ahi alo bhi blo) = 0 at hnamed
    unfold fpSubValue
    rw [if_neg hnamed]
    rfl

private theorem calldataSizeWord_ne {yst : EvmState}
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ Challenge.Bls12381G1Add.inputBytes) :
    BitVec.ofNat 256 yst.env.calldata.length ≠ BitVec.ofNat 256 256 := by
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hfit] at hnat
  apply hsize
  simpa [Challenge.Bls12381G1Add.inputBytes,
    Challenge.Bls12381.ProofSupport.Codec.g1Bytes] using hnat

private theorem exec_invalidLengthStmt {yst : EvmState} (funs V)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ Challenge.Bls12381G1Add.inputBytes) :
    Interp.execStmt modexpExec 113 funs V yst invalidLengthStmt =
      .ok (V, { yst with halted := some (.invalid, []) }, .halt) := by
  have hword := calldataSizeWord_ne hfit hsize
  simp [invalidLengthStmt, Interp.execStmt, Interp.execStmts,
    Interp.evalExpr, Interp.evalArgs, modexpExec, modexpBuiltinFn, stepOp,
    bin, un, rd0, litValue, b2w, Dialect.zero, restore, hword]

/-- A wrong calldata length takes the first source-level `invalid()` branch. -/
theorem run_invalid_length {yst : EvmState}
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hsize : yst.env.calldata.length ≠ Challenge.Bls12381G1Add.inputBytes)
    (_hhalted : yst.halted = none) :
    ∃ yst',
      Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
        referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.invalid, []) := by
  let yst' : EvmState := { yst with halted := some (.invalid, []) }
  refine ⟨yst', modexpExec_run_sound (fuel := 128) ?_, rfl⟩
  unfold Interp.run
  simp only [Interp.execStmt]
  rw [exec_reference_function_prefix]
  rw [Interp.execStmts]
  rw [exec_invalidLengthStmt _ _ hfit hsize]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
