import Challenge.EvmProof.Bytecode
import Challenge.EvmProof.Execution
import Challenge.EvmProof.Gas
import Challenge.EvmProof.GasFormula
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Ops
import Challenge.EvmProof.Program
import Challenge.EvmProof.Word
set_option warningAsError true
/-!
# Direct-bytecode proof support

Infrastructure for proofs that start from participant-supplied EVM bytecode:
a byte-preserving verified disassembler and direct `Step`/`Eval` proof
combinators. This layer has no source-language or compiler-correctness premise.
-/
