import EvmSemantics.EVM.BigStep

set_option warningAsError true

namespace Challenge.Bls12381MapFp2ToG2

open EvmSemantics EvmSemantics.EVM

def spec (input : ByteArray) : Option ByteArray :=
  Crypto.Bls12381MapFp2ToG2.run? input

def deployAddress : AccountAddress := AccountAddress.ofNat 0x8211

def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.blsMapFp2ToG2Address] }

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

end Challenge.Bls12381MapFp2ToG2

