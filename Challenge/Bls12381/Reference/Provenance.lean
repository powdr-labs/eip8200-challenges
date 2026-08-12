set_option warningAsError true

/-!
# Provenance for the BLS12-381 Solidity baselines

These values identify an independently authored, unverified implementation.
They are provenance data, not evidence of EIP-2537 conformance or correctness.
-/

namespace Challenge.Bls12381.Reference

def upstreamRepository : String := "https://github.com/eth-act/evmification.git"

def upstreamCommit : String := "a6da8572fee65cac4318b96fcf18f171d7587c21"

def upstreamTree : String := "3ac3a852641a926109cac89947e6d7bc8c7be8fc"

def upstreamSrcTree : String := "60af1b3b2a23e76a58ef6428e8a0b1235fb3487b"

def upstreamBlsFieldTree : String := "06bfdc0dfe110e684e2ea6d78bbb22d775f0aa3e"

def compilerVersion : String := "0.8.35+commit.47b9dedd"

def foundryVersion : String :=
  "forge 1.5.1-stable (b0a9dd9ceda36f63e2326ce530c10e6916f4b8a2)"

/-- Exact `forge-std` revision recorded by the upstream `foundry.lock`. -/
def forgeStdCommit : String :=
  "0844d7e1fc5e60d77b68e469bff60265f236c398"

/-- Exact OpenZeppelin Contracts revision recorded by the upstream
`foundry.lock`. -/
def openzeppelinCommit : String :=
  "fcbae5394ae8ad52d8e580a3477db99814b9d565"

def compilerSettings : List (String × String) :=
  [ ("viaIR", "true")
  , ("optimizer.enabled", "true")
  , ("optimizer.runs", "10000")
  , ("evmVersion", "osaka")
  , ("metadata.bytecodeHash", "ipfs")
  , ("metadata.cbor", "true") ]

/-- A reproducible rebuild starts from a clean checkout of `upstreamCommit`.
The explicit compiler selector closes the upstream `foundry.toml` gap: that
file enables automatic compiler detection instead of pinning a solc release. -/
def rebuildCommand : String :=
  "forge build --force --use 0.8.35"

def extractionExpression : String :=
  ".deployedBytecode.object"

/-- The upstream commit has no root LICENSE or COPYING file. Every Solidity
source reachable by these seven contracts declares `SPDX-License-Identifier:
MIT`; no copyright notice accompanies those declarations. This records the
available evidence and must not be read as legal clearance. -/
def licensingAudit : String :=
  "Per-file SPDX expression MIT; no root license text or copyright notice at the pinned commit."

/-- Shared warning for the baselines whose invalid-input behavior does not
match EIP-2537.  Keeping the text named lets checks pin both its wording and
its inclusion in the provenance record. -/
def rejectionSemanticsLimitation : String :=
  "Several upstream baselines accept inputs that EIP-2537 requires to be rejected; see knownNoncompliance."

def generalLimitations : List String :=
  [ "The files are deployed runtime bytecode, not creation bytecode."
  , "No Lean theorem connects any baseline artifact to a challenge specification."
  , "A successful rebuild establishes reproducibility only, not functional correctness."
  , "The upstream differential tests cover selected valid inputs and do not establish conformance."
  , "The upstream build emits compiler and lint warnings."
  , rejectionSemanticsLimitation
  , licensingAudit ]

def knownNoncompliance : List (String × String) :=
  [ ("G1ADD", "No known structural deviation found in this audit; arithmetic remains unproved.")
  , ("G1MSM", "Accepts empty input and omits the mandatory G1 subgroup check.")
  , ("G2ADD", "Does not reject nonzero padding, coordinates outside Fp, or non-curve points.")
  , ("G2MSM",
      "Accepts empty input and omits encoding, curve-membership, and mandatory subgroup checks.")
  , ("MAP_FP_TO_G1", "Does not reject nonzero padding or an input integer outside Fp.")
  , ("MAP_FP2_TO_G2", "Does not reject nonzero padding or input coefficients outside Fp.")
  , ("PAIRING",
      "Accepts empty input and explicitly omits mandatory G1 and G2 subgroup checks.") ]

end Challenge.Bls12381.Reference
