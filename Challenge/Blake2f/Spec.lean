import EvmSemantics.EVM.BigStep
set_option warningAsError true
/-!
# Ethereum BLAKE2f challenge statement

`Challenge.Blake2f.Correct` specifies the complete EIP-152 interface of the
`0x09` precompile: valid 213-byte inputs return the 64-byte compression result,
while malformed lengths and final flags halt exceptionally. The round count,
word decoder, compression function, and encoder are exactly those used by
`EvmSemantics.EVM.Precompile.runBlake2f` in the pinned semantics.
-/

namespace Challenge.Blake2f

open EvmSemantics
open EvmSemantics.EVM

/-- The four-byte big-endian round count at the head of an EIP-152 input. -/
def rounds (input : ByteArray) : Nat :=
  Data.Bytes.bytesToBigEndianNat (input.extract 0 4)

/-- Executable validity check from the BLAKE2f precompile wrapper. -/
def validInput (input : ByteArray) : Bool :=
  input.size == Precompile.blake2fInputLength &&
    (input[212]! == 0 || input[212]! == 1)

/-- Inputs on which the BLAKE2f precompile returns successfully. -/
def ValidInput (input : ByteArray) : Prop := validInput input = true

/-- Calldata sizes realizable at the protocol/runtime boundary. -/
def CalldataFits (input : ByteArray) : Prop := input.size < 2 ^ 64

/-- The successful result of the pinned BLAKE2f precompile. -/
def spec (input : ByteArray) : ByteArray :=
  Crypto.Blake2f.compressBytes input (rounds input)

/-- A non-precompile deployment address used until the semantics models the
post-EIP-8200 fork. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8209

/-- Disable the incumbent BLAKE2f precompile. A candidate therefore cannot
delegate its proof obligation by calling address `0x09`. -/
def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.blake2fAddress] }

/-- The explicit fixed Osaka frame used to judge candidates. -/
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

/-- The observable outcome required for one input. Invalid-input failures may
carry any EVM exception tag: like the incumbent precompile's `outOfGas`
result, every such exceptional callee consumes its frame gas and makes CALL
return zero. -/
def Matches (input : ByteArray) : ExecutionResult → Prop :=
  if validInput input then fun result => result = .returned (spec input)
  else fun result => ∃ exception, result = .exception exception

/-- **The challenge.** For every realizable calldata, every sufficiently large
gas budget produces the same successful-return versus exceptional-failure
behavior as the BLAKE2f precompile. -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      ∃ result, Eval (initialState code calldata g) result ∧ Matches calldata result

end Challenge.Blake2f
