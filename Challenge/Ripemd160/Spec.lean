import EvmSemantics.EVM.BigStep
set_option warningAsError true
/-!
# The Ethereum RIPEMD-160 challenge statement

`Challenge.Ripemd160.Correct` is the complete acceptance predicate for EVM
bytecode replacing Ethereum's `0x03` precompile. The expected result is the
precompile interface, not merely the raw hash: twelve leading zero bytes
followed by the 20-byte RIPEMD-160 digest.

The specification function below is built from the same
`EvmSemantics.Crypto.Ripemd160.hash` used by
`EvmSemantics.EVM.Precompile.runRipemd160` in the pinned semantics.
-/

namespace Challenge.Ripemd160

open EvmSemantics
open EvmSemantics.EVM

/-- Ethereum's `0x03` precompile result: the 20-byte digest right-aligned in a
32-byte return value. -/
def spec (input : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for _ in [0:12] do out := out.push 0
  return out ++ Crypto.Ripemd160.hash input

/-- Calldata sizes realizable at the protocol/runtime boundary. -/
def CalldataFits (input : ByteArray) : Prop := input.size < 2 ^ 64

/-- A non-precompile address used while the pinned fork still reserves `0x03`. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8200

/-- Disable the native RIPEMD-160 precompile for replacement executions. -/
def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.ripemd160Address] }

/-- The explicit fixed initial state used to judge candidates. -/
def initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let account : Account := { Account.empty with code }
  let accounts := AccountMap.empty.set deployAddress account
  let env : ExecutionEnv := {
    (default : ExecutionEnv) with
    address := deployAddress
    codeAddr := deployAddress
    origin := AccountAddress.ofNat 0
    caller := AccountAddress.ofNat 0
    weiValue := 0
    calldata
    code
    gasPrice := 0
    depth := 0
    permitStateMutation := true
    blobVersionedHashes := #[]
    fork := .Osaka
    precompileConfig := executionConfig
  }
  { (default : EVM.State) with
    pc := 0
    stack := []
    execLength := 0
    halt := .Running
    callStack := []
    gasAvailable := gas
    activeWords := 0
    memory := .empty
    returnData := .empty
    hReturn := .empty
    accountMap := accounts
    substate := { Substate.empty with originalAccountMap := accounts }
    executionEnv := env }

/-- **The challenge.** For every realizable calldata, every sufficiently large
gas budget makes `code` return exactly the padded output of Ethereum's
RIPEMD-160 precompile. -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
    Eval (initialState code calldata g) (.returned (spec calldata))

end Challenge.Ripemd160
