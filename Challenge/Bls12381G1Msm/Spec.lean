import EvmSemantics.EVM.BigStep
import Challenge.Bls12381.ProofSupport.CodecSubgroup
import Challenge.Bls12381.ProofSupport.CodecScalar
import Challenge.Bls12381.ProofSupport.Msm

set_option warningAsError true

namespace Challenge.Bls12381G1Msm

open EvmSemantics EvmSemantics.EVM

def pairBytes : Nat := 160

open Challenge.Bls12381.ProofSupport

/-- Package the exact unsigned scalar window independently of the success
proof used to establish that the complete window is present. -/
def scalarAt (input : ByteArray) (offset : Nat) : ScalarMul.Scalar256 :=
  ⟨Codec.scalarWindowValue input offset,
    Codec.scalarWindowValue_lt input offset⟩

/-- Decode one exact EIP-2537 `(G1, scalar)` term.  The point decoder includes
the mandatory subgroup check, while the scalar is retained as the full
unreduced unsigned 256-bit wire value. -/
def decodeTerm (input : ByteArray) (offset : Nat) : Option Msm.G1WireTerm := do
  (Codec.decodeG1Subgroup input offset).bind fun point =>
    match Codec.decodeScalar input (offset + Codec.g1Bytes) with
    | none => none
    | some _ =>
        some (point, scalarAt input (offset + Codec.g1Bytes))

/-- Decode `count` consecutive terms, preserving their wire order. -/
def decodeTerms (input : ByteArray) (offset : Nat) :
    Nat → Option (List Msm.G1WireTerm)
  | 0 => some []
  | count + 1 => do
      let term ← decodeTerm input offset
      let rest ← decodeTerms input (offset + pairBytes) count
      some (term :: rest)

/-- EIP-2537-conformant G1MSM core using the local proof-visible codecs and
the shared naive left-fold MSM. -/
def spec (input : ByteArray) : Option ByteArray := do
  if input.size = 0 ∨ input.size % pairBytes ≠ 0 then none
  else
  let terms ← decodeTerms input 0 (input.size / pairBytes)
  return Codec.encodeG1 (Msm.g1Wire terms)

def deployAddress : AccountAddress := AccountAddress.ofNat 0x820c

def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.blsG1MsmAddress] }

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

def Matches (input : ByteArray) : ExecutionResult → Prop :=
  match spec input with
  | some output => fun result => result = .returned output
  | none => fun result => ∃ exception, result = .exception exception

def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, calldata.size < 2 ^ 64 →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      ∃ result, Eval (initialState code calldata g) result ∧ Matches calldata result

end Challenge.Bls12381G1Msm
