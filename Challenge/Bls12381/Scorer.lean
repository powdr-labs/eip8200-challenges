import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex

set_option warningAsError true

/-!
# Shared BLS12-381 executable scorer

The seven EIP-2537 challenges have the same execution contract: valid input
returns the specified bytes, while malformed input terminates exceptionally.
This module keeps that executable falsification harness in one place.  It is
deliberately independent of every individual challenge module.
-/

namespace Challenge.Bls12381.Scorer

open EvmSemantics EvmSemantics.EVM

structure Config where
  spec : ByteArray → Option ByteArray
  initialState : ByteArray → ByteArray → Nat → EVM.State

structure Vector where
  label : String
  input : ByteArray

def scoringGas : Nat := 3_000_000_000_000
def scoringFuel : Nat := 500_000_000

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

inductive Outcome where
  | ok (gas : Nat)
  | wrongResult (got expected : Option String) (gas : Nat)
  | badHalt (halt : String) (gas : Nat)
  | outOfFuel
deriving Repr

def Outcome.gas? : Outcome → Option Nat
  | .ok gas | .wrongResult _ _ gas | .badHalt _ gas => some gas
  | .outOfFuel => none

private def outputHex : Option ByteArray → Option String
  | none => none
  | some output => some (Hex.bytesToHex output)

/-- Execute one candidate/vector pair.  Exceptional halts are accepted exactly
when the specification rejects the input. -/
def score (config : Config) (code input : ByteArray) : Outcome :=
  let start := config.initialState code input scoringGas
  let final := runEvm scoringFuel start
  if !final.isDone then .outOfFuel else
  let gas := start.gasAvailable - final.gasAvailable
  let expected := config.spec input
  match final.halt, expected with
  | .Returned, some output =>
      if final.hReturn == output then .ok gas
      else .wrongResult (some (Hex.bytesToHex final.hReturn)) (some (Hex.bytesToHex output)) gas
  | .Returned, none =>
      .wrongResult (some (Hex.bytesToHex final.hReturn)) none gas
  | .Exception _, none => .ok gas
  | .Exception _, some output => .wrongResult none (outputHex (some output)) gas
  | halt, _ => .badHalt (toString (repr halt)) gas

def zeros (n : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for _ in [:n] do
    bytes := bytes.push 0
  return bytes

def patterned (n : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [:n] do
    bytes := bytes.push (UInt8.ofNat ((i * 37 + 11) % 256))
  return bytes

end Challenge.Bls12381.Scorer
