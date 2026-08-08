import Checks.EvmProof
import Checks.Blake2f
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
