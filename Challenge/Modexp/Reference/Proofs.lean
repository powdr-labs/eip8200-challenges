import Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect
import Challenge.Modexp.Reference.Proofs.Gas
import Challenge.Modexp.Reference.Proofs.Yul

/-!
# Correctness and gas proof for the bundled MODEXP reference

Correctness routes for the frozen 1,284-byte artifact.  The direct-bytecode
proof establishes functional correctness and exact gas.  The source-Yul route
proves the readable program directly in the relational semantics, then pins
parsing, optimization, verified compilation, and assembly to the same frozen
artifact.
-/
