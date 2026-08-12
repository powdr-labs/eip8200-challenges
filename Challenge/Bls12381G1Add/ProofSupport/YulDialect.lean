import Challenge.EvmProof.ModexpCalls
import YulEvmCompiler.AsmSem

set_option warningAsError true

/-! Lightweight source-dialect boundary shared by executable artifacts. -/

namespace Challenge.Bls12381G1Add.ProofSupport.Yul

open YulSemantics.EVM (evmWithExternal ExternalCreates)
open YulEvmCompiler (ExternalModel)
open Challenge.EvmProof

@[reducible] def localModel : ExternalModel where
  calls := successfulModexpCalls
  creates := ExternalCreates.none

abbrev localDialect :=
  evmWithExternal successfulModexpCalls ExternalCreates.none

end Challenge.Bls12381G1Add.ProofSupport.Yul
