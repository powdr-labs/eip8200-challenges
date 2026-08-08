import Challenge.Blake2f.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
set_option warningAsError true

/-! Executable BLAKE2f vectors, failure cases, and frame-gas measurement. -/

namespace Challenge.Blake2f.Scorer

open EvmSemantics
open Challenge.Blake2f

def scoringGas : Nat := 3_000_000_000
def scoringFuel : Nat := 300_000_000

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

def dirtyInitialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let state := initialState code calldata gas
  let account := state.accountMap deployAddress
  let account := { account with
    storage := account.storage.set 0 0xdeadbeef
    tstorage := account.tstorage.set 0 7 }
  let accounts := state.accountMap.set deployAddress account
  { state with
    accountMap := accounts
    substate := { state.substate with originalAccountMap := accounts }
    executionEnv := { state.executionEnv with weiValue := 0x1234 } }

/-- Chaining state from the EIP-152 BLAKE2b-512 vectors. -/
def hBytes : ByteArray := Hex.hexToBytes
  ("48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
   "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b")

/-- Assemble one exact 213-byte EIP-152 input. -/
def buildInput (roundCount : Nat) (message : ByteArray) (t0 t1 : Nat)
    (finalFlag : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:4] do
    out := out.push (UInt8.ofNat ((roundCount >>> (8 * (3 - i))) &&& 0xff))
  out := out ++ hBytes ++ message
  for _ in [0:128 - message.size] do out := out.push 0
  for i in [0:8] do out := out.push (UInt8.ofNat ((t0 >>> (8 * i)) &&& 0xff))
  for i in [0:8] do out := out.push (UInt8.ofNat ((t1 >>> (8 * i)) &&& 0xff))
  return out.push finalFlag

def abcInput (roundCount : Nat) (finalFlag : UInt8) : ByteArray :=
  buildInput roundCount "abc".toUTF8 3 0 finalFlag

structure Vector where
  label : String
  input : ByteArray
  valid : Bool := true

def vectors : List Vector :=
  [ { label := "0 rounds, f=0", input := abcInput 0 0 }
  , { label := "0 rounds, f=1", input := abcInput 0 1 }
  , { label := "1 round", input := abcInput 1 1 }
  , { label := "2 rounds", input := abcInput 2 1 }
  , { label := "9 rounds", input := abcInput 9 1 }
  , { label := "10 rounds", input := abcInput 10 1 }
  , { label := "11 rounds", input := abcInput 11 1 }
  , { label := "12 rounds, f=0", input := abcInput 12 0 }
  , { label := "12 rounds, f=1", input := abcInput 12 1 }
  , { label := "100 rounds", input := abcInput 100 1 }
  , { label := "212-byte invalid", input := (abcInput 12 1).extract 0 212,
      valid := false }
  , { label := "214-byte invalid", input := (abcInput 12 1).push 0,
      valid := false }
  , { label := "flag=2 invalid", input := abcInput 12 2, valid := false } ]

/-- Published EIP-152 outputs used to independently sanity-check the spec. -/
def oracleChecks : List (ByteArray × String) :=
  [ (abcInput 12 1,
      "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
      "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")
  , (abcInput 12 0,
      "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752" ++
      "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735")
  , (abcInput 0 1,
      "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
      "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b")
  , (abcInput 1 1,
      "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
      "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421") ]

inductive Outcome where
  | ok (gas : Nat)
  | wrongResult (description : String) (gas : Nat)
  | outOfFuel

def Outcome.gas? : Outcome → Option Nat
  | .ok gas | .wrongResult _ gas => some gas
  | .outOfFuel => none

def score (mkInitialState : ByteArray → ByteArray → Nat → EVM.State)
    (code calldata : ByteArray) : Outcome :=
  let start := mkInitialState code calldata scoringGas
  let final := runEvm scoringFuel start
  if !final.isDone then .outOfFuel else
  let gas := start.gasAvailable - final.gasAvailable
  if validInput calldata then
    match final.halt with
    | .Returned =>
        if final.hReturn == spec calldata then .ok gas
        else .wrongResult s!"wrong output {Hex.bytesToHex final.hReturn}" gas
    | halt => .wrongResult s!"expected RETURN, got {repr halt}" gas
  else
    match final.halt with
    | .Exception _ => .ok gas
    | halt => .wrongResult s!"expected exception, got {repr halt}" gas

def verdict (code : ByteArray) (v : Vector) : Outcome × Outcome × String :=
  let clean := score initialState code v.input
  let dirty := score dirtyInitialState code v.input
  let status :=
    match clean, dirty with
    | .ok g1, .ok g2 =>
        if g1 == g2 then "ok" else s!"ok (state-dependent gas: {g1} vs {g2})"
    | .wrongResult why _, _ => s!"WRONG: {why}"
    | _, .wrongResult why _ => s!"WRONG (dirty): {why}"
    | .outOfFuel, _ | _, .outOfFuel => "OUT OF FUEL"
  (clean, dirty, status)

end Challenge.Blake2f.Scorer
