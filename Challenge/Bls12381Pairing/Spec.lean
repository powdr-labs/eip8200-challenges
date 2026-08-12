import EvmSemantics.EVM.BigStep
import Challenge.Bls12381.ProofSupport.Subgroup

set_option warningAsError true

namespace Challenge.Bls12381Pairing

open EvmSemantics EvmSemantics.EVM

def pairBytes : Nat := 384

abbrev inG1Subgroup := Challenge.Bls12381.ProofSupport.Subgroup.g1

def decodePairs (input : ByteArray) :
    Option (List (Crypto.Bls12381.Point × Crypto.Bls12381.G2Point)) := Id.run do
  if input.size = 0 ∨ input.size % pairBytes ≠ 0 then return none
  let k := input.size / pairBytes
  let mut pairs := []
  for i in [0:k] do
    let off := i * pairBytes
    match Crypto.Bls12381G1Add.decodePoint input off,
        Crypto.Bls12381G2Add.decodePoint input (off + 128) with
    | some p, some q =>
      if !inG1Subgroup p || !Challenge.Bls12381.ProofSupport.Subgroup.g2 q then
        return none
      pairs := (p, q) :: pairs
    | _, _ => return none
  return some pairs.reverse

/-- EIP-2537-conformant core. This adds both subgroup checks omitted by the
pinned `Bls12381PairingCheck.run?` wrapper. -/
def spec (input : ByteArray) : Option ByteArray := do
  let pairs ← decodePairs input
  let isOne : Bool := decide
    (Crypto.Bls12381Pairing.multiPairing pairs = (1 : Crypto.Bls12381.Fp12))
  some (Data.Bytes.natToBytesPadded (if isOne then 1 else 0) 32)

def deployAddress : AccountAddress := AccountAddress.ofNat 0x820f

def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.blsPairingAddress] }

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

end Challenge.Bls12381Pairing
