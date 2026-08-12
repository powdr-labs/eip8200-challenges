import Checks.EvmProof
import Checks.EvmProofModPow
import Checks.Blake2f
import Checks.Bls12381Codec
import Checks.Bls12381Conformance
import Checks.Bls12381Fp
import Checks.Bls12381Fp2
import Checks.Bls12381Fp6
import Checks.Bls12381Fp12
import Checks.Bls12381G1Projective
import Checks.Bls12381G2Projective
import Checks.Bls12381ScalarMul
import Checks.Bls12381Msm
import Checks.Bls12381PrimeField
import Checks.Bls12381PrimeCertificate
import Checks.Modexp
import Checks.Ripemd160
import Checks.Sha256
set_option warningAsError true
/-!
# Checks

Umbrella for the CI axiom-footprint checks. CI type-checks the imported
modules independently so a change to one challenge does not invalidate the
other challenges' builds or caches.
-/
