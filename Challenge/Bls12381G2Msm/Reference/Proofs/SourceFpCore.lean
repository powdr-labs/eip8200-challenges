import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpPredicates

set_option warningAsError true

/-! # Remaining frozen G2MSM scalar-field helpers -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

abbrev fpValidValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpValidValue
abbrev fpEqValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpEqValue
abbrev fpAddValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpAddValue
abbrev fpSubRawValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpSubRawValue
abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue
abbrev fpSubValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpSubValue
abbrev FullMulValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.FullMulValue
abbrev fullMulValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fullMulValue
abbrev fpModulusHiValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpModulusHiValue
abbrev fpModulusLoValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpModulusLoValue
abbrev storeFpState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.storeFpState

export Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
  (conv_fpValidValue conv_fpEqValue conv_fullMulValue
    bytesNat_readBytes_storeFpState)

theorem conv_fpAddValue (ahi alo bhi blo : U256) :
    ({ hi := YulEvmCompiler.conv (fpAddValue ahi alo bhi blo).1,
       lo := YulEvmCompiler.conv (fpAddValue ahi alo bhi blo).2 } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) =
    Challenge.Bls12381.ProofSupport.Fp.addSource
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.conv_fpAddValue
    ahi alo bhi blo

theorem conv_fpSubValue (ahi alo bhi blo : U256) :
    ({ hi := YulEvmCompiler.conv (fpSubValue ahi alo bhi blo).1,
       lo := YulEvmCompiler.conv (fpSubValue ahi alo bhi blo).2 } :
      Challenge.Bls12381.ProofSupport.Fp.Limbs) =
    Challenge.Bls12381.ProofSupport.Fp.subSource
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.conv_fpSubValue
    ahi alo bhi blo

theorem eval_fpValid (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [fpValidValue hi lo] yst) := by
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

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
