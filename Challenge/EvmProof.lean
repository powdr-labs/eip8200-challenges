import Challenge.EvmProof.Bytecode
import Challenge.EvmProof.ByteWindow
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.Execution
import Challenge.EvmProof.ExecSound
import Challenge.EvmProof.Gas
import Challenge.EvmProof.GasFormula
import Challenge.EvmProof.Limbs
import Challenge.EvmProof.Memory
import Challenge.EvmProof.MemoryRegion
import Challenge.EvmProof.ModexpCalls
import Challenge.EvmProof.ModexpCallRealization
import Challenge.EvmProof.ModexpExec
import Challenge.EvmProof.ModexpMemory
import Challenge.EvmProof.ModexpOne
import Challenge.EvmProof.Ops
import Challenge.EvmProof.Program
import Challenge.EvmProof.ProfiledCalls
import Challenge.EvmProof.ProfiledCorrectness
import Challenge.EvmProof.ProfiledSteps
import Challenge.EvmProof.Word
set_option warningAsError true
/-!
# Direct-bytecode proof support

Infrastructure for proofs that start from participant-supplied EVM bytecode:
a byte-preserving verified disassembler and direct `Step`/`Eval` proof
combinators. This layer has no source-language or compiler-correctness premise.
-/
