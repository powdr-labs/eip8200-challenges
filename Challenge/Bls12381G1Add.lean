import Challenge.Bls12381G1Add.Spec
import Challenge.Bls12381G1Add.YulSpec
import Challenge.Bls12381G1Add.Reference
import Challenge.Bls12381G1Add.Reference.Proofs

/-!
# BLS12-381 G1ADD source challenge

Start with `Spec.lean` and `YulSpec.lean`. The reference proof establishes the
Yul source contract only; the generated EVM artifact is exercised by Foundry
and is not the subject of a compiler or bytecode correctness theorem.
-/
