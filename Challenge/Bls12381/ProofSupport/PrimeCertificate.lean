import Challenge.Bls12381.ProofSupport.PrimeCertificate.Root

set_option warningAsError true

/-!
# Kernel-checked BLS12-381 primality certificate

Dependency-ordered certificate modules keep each kernel elaboration unit
memory-bounded.  This umbrella exposes the complete fixed-modulus proof.
-/
