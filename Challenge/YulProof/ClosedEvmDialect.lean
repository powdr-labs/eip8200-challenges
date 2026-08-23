import YulSemantics.Dialect.EVMExec

set_option warningAsError true

/-!
# Closed EVM dialect for source-Yul specifications

This module fixes the source semantics used by local challenge programs while
depending only on `yul-semantics`.  Executability, lawfulness, and compiler
transport live in `Challenge.YulProof.ClosedEvm`.
-/

namespace Challenge.YulProof.ClosedEvm

open YulSemantics.EVM (evmWithExternal ExternalCalls ExternalCreates ExternalGas)

/-- Gas-free EVM source dialect with no external calls or creations. -/
abbrev dialect := evmWithExternal ExternalCalls.none ExternalCreates.none ExternalGas.none

end Challenge.YulProof.ClosedEvm
