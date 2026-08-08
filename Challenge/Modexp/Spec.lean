import EvmSemantics.EVM.BigStep
set_option warningAsError true
/-!
# Ethereum MODEXP challenge statement

`Challenge.Modexp.Correct` is the acceptance predicate for bytecode replacing
the successful domain of Ethereum's `0x05` precompile after Osaka.  The
operand parser, arbitrary-precision modular exponentiation, and fixed-width
encoder are the same definitions used by `Precompile.runModexp` in the pinned
EVM semantics.
-/

namespace Challenge.Modexp

open EvmSemantics
open EvmSemantics.EVM

/-- Base-byte length declared by the first EIP-198 header word. -/
def baseSize (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 0 32

/-- Exponent-byte length declared by the second EIP-198 header word. -/
def exponentSize (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 32 32

/-- Modulus-byte length declared by the third EIP-198 header word. -/
def modulusSize (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 64 32

/-- The successful Osaka/EIP-7823 domain.  Inputs whose declared sizes exceed
1024 bytes fail exceptionally in the precompile and are covered separately
from the return-value equivalence challenge. -/
def ValidInput (input : ByteArray) : Prop :=
  input.size < 2 ^ 64 ∧
    baseSize input ≤ 1024 ∧ exponentSize input ≤ 1024 ∧ modulusSize input ≤ 1024

/-- The bytes returned by the MODEXP precompile for a valid EIP-198 tuple.
Missing operand bytes are zero-padded at the tail by `bytesToNatPadded`. -/
def spec (input : ByteArray) : ByteArray :=
  let bsize := baseSize input
  let esize := exponentSize input
  let msize := modulusSize input
  if msize = 0 then ByteArray.empty
  else
    let b := Precompile.bytesToNatPadded input 96 bsize
    let e := Precompile.bytesToNatPadded input (96 + bsize) esize
    let m := Precompile.bytesToNatPadded input (96 + bsize + esize) msize
    Precompile.natToBytes (Precompile.modPow b e m) msize

/-- Non-precompile deployment address used until the pinned semantics models
the post-EIP-8200 fork. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8205

/-- Disable the native MODEXP precompile for replacement executions. -/
def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.modexpAddress] }

/-- Explicit fixed initial state used to judge a MODEXP candidate. -/
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

/-- **The challenge.** Every valid MODEXP tuple returns the precompile result
for every sufficiently large gas budget. -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ValidInput calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval (initialState code calldata g) (.returned (spec calldata))

end Challenge.Modexp
