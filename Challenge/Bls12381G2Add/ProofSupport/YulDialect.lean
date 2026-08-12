import Challenge.EvmProof.ModexpCalls
import YulEvmCompiler.AsmSem

set_option warningAsError true

/-! Lightweight source-dialect boundary for the G2ADD executable artifact. -/

namespace Challenge.Bls12381G2Add.ProofSupport.Yul

open YulSemantics.EVM (evmWithExternal ExternalCreates)
open YulEvmCompiler (ExternalModel)
open Challenge.EvmProof

@[reducible] def localModel : ExternalModel where
  calls := successfulModexpCalls
  creates := ExternalCreates.none

abbrev localDialect :=
  evmWithExternal successfulModexpCalls ExternalCreates.none

end Challenge.Bls12381G2Add.ProofSupport.Yul

