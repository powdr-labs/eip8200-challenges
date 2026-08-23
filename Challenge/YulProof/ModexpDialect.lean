import Challenge.EvmProof.ModexpCalls
import YulSemantics.Dialect.EVMExec

set_option warningAsError true

/-!
# MODEXP-only EVM source dialect

This reusable high-level dialect admits successful Osaka `staticcall`s to
MODEXP (`0x05`) and no other external call or contract creation. Programs
proved in it therefore cannot delegate to the precompile they implement.
-/

namespace Challenge.YulProof.Modexp

open YulSemantics.EVM (evmWithExternal ExternalCreates ExternalGas)
open Challenge.EvmProof

abbrev dialect :=
  evmWithExternal successfulModexpCalls ExternalCreates.none ExternalGas.any

end Challenge.YulProof.Modexp
