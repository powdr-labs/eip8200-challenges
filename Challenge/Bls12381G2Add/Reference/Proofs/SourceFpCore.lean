import Challenge.Bls12381G2Add.Reference.Proofs.Compilation
import Challenge.Bls12381G1Add.Reference.Proofs.SourceStore

set_option warningAsError true

/-!
# Scalar-field source helpers shared by G1ADD and G2ADD

The first nine helpers in the frozen G2ADD source are source-identical to the
corresponding G1ADD helpers.  Their pure value graphs and representation
proofs are therefore reused here, while the evaluator theorems below are
checked against the G2ADD frozen block itself.  This keeps the implementation
dependency explicit without repeating the expensive arithmetic proofs.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof
open Challenge.Bls12381G2Add.Reference.Proofs.Compilation

abbrev fpGeModulusValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
abbrev fpValidValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpValidValue
abbrev fpZeroValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue
abbrev fpEqValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpEqValue
abbrev fpAddValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue
abbrev fpSubRawValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue
abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue
abbrev fpSubRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue
abbrev fpSubValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue

abbrev FullWordValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.FullWordValue
abbrev FullMulValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.FullMulValue
abbrev FullMulMiddleValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.FullMulMiddleValue
abbrev mulModMersenneValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mulModMersenneValue
abbrev fullWordValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fullWordValue
abbrev fullMulMiddleValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fullMulMiddleValue
abbrev fullMulValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fullMulValue

abbrev fpModulusHiValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue
abbrev fpModulusLoValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusLoValue
abbrev storeFpState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.storeFpState

export Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
  (conv_fpGeModulusValue conv_fpValidValue conv_fpZeroValue conv_fpEqValue
    conv_fullMulValue bytesNat_readBytes_storeFpState)

/-- The reused G1 value graph refines the shared source-faithful Fp addition
schedule; the local wrapper gives downstream G2 proofs a stable boundary. -/
theorem conv_fpAddValue (ahi alo bhi blo : U256) :
    ({ hi := YulEvmCompiler.conv (fpAddValue ahi alo bhi blo).1,
       lo := YulEvmCompiler.conv (fpAddValue ahi alo bhi blo).2 } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) =
    Challenge.Bls12381.ProofSupport.Fp.addSource
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpAddValue
    ahi alo bhi blo

/-- The reused G1 value graph refines the shared source-faithful Fp
subtraction schedule. -/
theorem conv_fpSubValue (ahi alo bhi blo : U256) :
    ({ hi := YulEvmCompiler.conv (fpSubValue ahi alo bhi blo).1,
       lo := YulEvmCompiler.conv (fpSubValue ahi alo bhi blo).2 } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) =
    Challenge.Bls12381.ProofSupport.Fp.subSource
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubValue
    ahi alo bhi blo

/-- The first G2ADD helper implements the shared high-first modulus test. -/
theorem eval_fpGeModulus (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x000" [.var "hi", .var "lo"]) =
    .ok (.vals [fpGeModulusValue hi lo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookupFun, hoist, referenceCompiledBlock, frozenReferenceBlock,
    modexpExec, modexpBuiltinFn, stepOp, bin, un, fpGeModulusValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpGeModulusValue,
    Dialect.zero, restore]
  rfl

theorem eval_fpValid (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [fpValidValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

theorem eval_fpZero (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x002" [.var "hi", .var "lo"]) =
    .ok (.vals [fpZeroValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

theorem eval_fpEq (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x003" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [fpEqValue ahi alo bhi blo] yst) := by
  rw [Interp.evalExpr]
  rfl

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
    simp [fpAddValue,
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue,
      hnamed]
  case isFalse hsource =>
    have hnamed := hsource
    change ¬fpGeModulusValue
      (ahi + bhi + b2w (BitVec.ult (alo + blo) alo)) (alo + blo) = 0 at hnamed
    unfold fpAddValue
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpAddValue
    rw [if_neg hnamed]
    rfl

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
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
    rw [if_pos hnamed]
    rfl
  case isFalse hsource =>
    have hnamed := hsource
    change ¬fpSubNeedsRepairValue (fpSubRawValue ahi alo bhi blo) = 0 at hnamed
    unfold fpSubValue
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
    rw [if_neg hnamed]
    rfl

theorem eval_fullMul (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x006" [.var "ahi", .var "alo", .var "bhi", .var "blo"]) =
    .ok (.vals [(fullMulValue ahi alo bhi blo).r2,
      (fullMulValue ahi alo bhi blo).r1,
      (fullMulValue ahi alo bhi blo).r0] yst) := by
  rw [Interp.evalExpr]
  rfl

theorem eval_storeFp (ptr hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("ptr", ptr), ("hi", hi), ("lo", lo)] yst
      (.call "\x007" [.var "ptr", .var "hi", .var "lo"]) =
    .ok (.vals [] (storeFpState yst ptr hi lo)) := by
  rw [Interp.evalExpr]
  rfl

theorem eval_storeModulus (ptr : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("ptr", ptr)] yst (.call "\x008" [.var "ptr"]) =
    .ok (.vals [] (storeFpState yst ptr fpModulusHiValue fpModulusLoValue)) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
