import Challenge.Modexp.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
set_option warningAsError true

/-!
# MODEXP executable falsification checks

The scorer compares candidate returndata with the pinned precompile-level
`spec`.  It includes the EIP-198 examples, edge cases, trailing-zero input
normalization, and a >256-bit modulus that exercises the multi-limb path.
-/

namespace Challenge.Modexp.Scorer

open EvmSemantics
open Challenge.Modexp

def scoringGas : Nat := 1_000_000_000_000
def scoringFuel : Nat := 500_000_000

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

structure Vector where
  label : String
  input : ByteArray

private def fromHex (hex : String) : ByteArray := Hex.hexToBytes hex

private def word (n : Nat) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded n 32

private def operand (n width : Nat) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded n width

def makeInput (base exponent modulus bsize esize msize : Nat) : ByteArray :=
  word bsize ++ word esize ++ word msize ++
    operand base bsize ++ operand exponent esize ++ operand modulus msize

/-- The exponent prefix used by the Osaka/EIP-7883 precompile gas formula. -/
def exponentHead (input : ByteArray) : Nat :=
  let size := Nat.min (exponentSize input) 32
  EVM.Precompile.bytesToNatPadded input (96 + baseSize input) size

/-- Gas charged by the pinned Osaka MODEXP precompile for this tuple. -/
def precompileGas (input : ByteArray) : Nat :=
  EVM.Precompile.modexpGas .Osaka (baseSize input) (exponentSize input)
    (modulusSize input) (exponentHead input)

def eipExample1 : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000001" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "03" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")

def eipExample2 : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000000" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")

/-- EIP-198's truncated-input example: the one supplied modulus byte is
interpreted as `0x80` followed by 31 zero bytes. -/
def truncatedModulus : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000001" ++
   "0000000000000000000000000000000000000000000000000000000000000002" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "03ffff80")

def vectors : List Vector :=
  [ { label := "empty tuple", input := ByteArray.empty }
  , { label := "2^5 mod 13", input := makeInput 2 5 13 1 1 1 }
  , { label := "zero exponent", input := makeInput 42 0 97 1 0 1 }
  , { label := "zero modulus", input := makeInput 42 7 0 1 1 12 }
  , { label := "zero modulus size", input := makeInput 42 7 0 1 1 0 }
  , { label := "EIP-198 example 1", input := eipExample1 }
  , { label := "EIP-198 example 2", input := eipExample2 }
  , { label := "trailing-zero normalization", input := truncatedModulus }
  , { label := "257-bit modulus"
    , input := makeInput (2 ^ 256 + 5) 3 (2 ^ 256 + 7) 33 1 33 }
  ]

inductive Outcome where
  | ok (gas : Nat)
  | wrongResult (got expected : String) (gas : Nat)
  | badHalt (halt : String) (gas : Nat)
  | outOfFuel

def Outcome.gas? : Outcome → Option Nat
  | .ok gas | .wrongResult _ _ gas | .badHalt _ gas => some gas
  | .outOfFuel => none

def score (code input : ByteArray) : Outcome :=
  let start := initialState code input scoringGas
  let final := runEvm scoringFuel start
  if !final.isDone then .outOfFuel else
  let gas := start.gasAvailable - final.gasAvailable
  match final.halt with
  | .Returned =>
      let expected := spec input
      if final.hReturn == expected then .ok gas
      else .wrongResult (Hex.bytesToHex final.hReturn) (Hex.bytesToHex expected) gas
  | halt => .badHalt (toString (repr halt)) gas

end Challenge.Modexp.Scorer
