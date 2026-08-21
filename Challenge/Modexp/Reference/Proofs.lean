import Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect
import Challenge.Modexp.Reference.Proofs.Gas
import Challenge.Modexp.Reference.Proofs.Yul

/-!
# Correctness and gas proof for the bundled MODEXP reference

Correctness routes for the frozen 1,284-byte artifact.  The direct-bytecode
proof establishes functional correctness and exact gas; the source-Yul route
pins parsing, optimization, verified compilation, and assembly while exposing
the direct source semantics as a separate proof obligation.
-/
