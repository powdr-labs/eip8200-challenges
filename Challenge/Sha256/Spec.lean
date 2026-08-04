import EvmSemantics.EVM.BigStep
set_option warningAsError true
/-!
# The SHA-256 challenge statement

One `Prop` that any candidate EVM bytecode — ours or a challenger's — must
satisfy to count as a verified replacement for the `0x02` precompile
(EIP-8200 / EIP-7666 "EVMification"): `Challenge.Sha256.Correct`.

## What the spec side is

Not ours. `EvmSemantics.Crypto.Sha256.hash` is the function the *precompile
itself* computes in the pinned `evm-semantics` dependency — see
`EvmSemantics.EVM.Precompile.runSha256`, which is literally
`.success (Crypto.Sha256.hash input) cost`. So "this bytecode is equivalent
to the SHA-256 precompile" is a statement *inside* the trusted semantics,
and the equality is against the same function the reference EVM already
uses. Nothing about the specification is this repository's to get wrong; it
is FIPS 180-4 as pinned and vector-checked by `evm-semantics`
(`tests/Sha256Test.lean` covers the published §B.1–B.3 vectors).

## What a submission must prove

`Correct code`: for every realizable calldata, given enough gas, the initial
EVM state executing
`code` halts by *returning* exactly the 32 digest bytes. Notably it does
**not** talk about our bytecode, our Yul, our memory layout, or our gas —
two implementations that both satisfy `Correct` are automatically
interchangeable on the interface a caller can observe. That is what makes
this a challenge statement rather than a description of one implementation:
equivalence to the spec, not equivalence to the incumbent's code.

## Scope, stated honestly

* `initialState` below is the repository's fixed judging state: fresh memory,
  empty storage, zero balance, zero call value, depth 0, Osaka. It is not an
  Ethereum object called "the canonical frame." A call always starts with fresh
  memory, but caller, call value, and surrounding world state can vary. Thus a
  submission that reads `SLOAD`/`CALLVALUE`/`CALLER` is constrained here only at
  the fixed values below. `CorrectInAnyContext` under `AdditionalGoals/` states
  the stronger context-independent property.
* `deployAddress` is *not* `0x02`. In the pinned Osaka semantics `0x02` is
  still a precompile (`Precompile.isPrecompile … = true`), so an initial state there
  never executes bytecode at all — flipping that bit is exactly what
  EIP-8200 activation does. Until the pinned semantics has a post-8200
  fork, the challenge runs the candidate at a non-precompile address, which
  is what the deployed code will be doing after activation.
-/

namespace Challenge.Sha256

open EvmSemantics
open EvmSemantics.EVM

/-! ## The specification -/

/-- The canonical SHA-256: the function the `0x02` precompile computes in the
pinned semantics (`Precompile.runSha256`). -/
def spec (input : ByteArray) : ByteArray := Crypto.Sha256.hash input

/-- Calldata sizes representable by the protocol/runtime boundary.  Lean's
logical `Array` type has no intrinsic size bound, whereas an EVM program sees
`CALLDATASIZE` through a 256-bit word.  The much tighter 64-bit bound captures
all realizable Ethereum inputs and prevents the challenge from quantifying
over mathematical arrays no EVM execution environment can represent. -/
def CalldataFits (input : ByteArray) : Prop := input.size < 2 ^ 64

/-! ## The initial state a candidate is judged in -/

/-- Where the challenge deploys a candidate. Any non-precompile address will
do; `0x8200` names the EIP. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8200

/-- Disable the native SHA-256 precompile for replacement executions. -/
def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.sha256Address] }

/-- The fixed initial EVM state used by the challenge: `code` deployed at
`deployAddress`, `calldata` as input, `gas` available, and everything else at
its zero — fresh memory, no storage, no transient storage, no balance, no call
value, depth 0, Osaka.

The constructor makes every environmental assumption in `Correct` explicit. -/
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

/-! ## The challenge -/

/-- **The challenge.** `code` computes SHA-256 the way the precompile does:
for every realizable calldata there is a gas level above which execution from
`initialState` halts by returning exactly the digest of that calldata.

`CalldataFits` excludes only logical arrays of at least `2^64` bytes. Such
arrays exist in Lean's unbounded model but cannot cross an Ethereum/runtime
boundary, and `CALLDATASIZE` could not represent their length faithfully.

The `∃ g₀, ∀ g ≥ g₀` shape is "given enough gas": gas *must* appear, since
below some level every implementation runs out, and no fixed constant can
be right for all input lengths. It carries real content — the conclusion
holds for every larger budget, so a candidate cannot pass by succeeding at
one lucky gas value. -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, CalldataFits calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
    Eval (initialState code calldata g) (.returned (spec calldata))

end Challenge.Sha256
