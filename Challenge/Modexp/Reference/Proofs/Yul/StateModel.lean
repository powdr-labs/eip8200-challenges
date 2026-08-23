import Challenge.Modexp.Reference.Proofs.Yul.Program
import Challenge.YulProof.EvmState

set_option warningAsError true

/-!
# Exact state model for the MODEXP source word path

The definitions in this file mirror the source-level `modexpWord` procedure.
They deliberately use Yul's `BitVec 256` values rather than the bytecode
proof's distinct `UInt256` wrapper.  This keeps the relational contracts in
`Word` definitionally close to the source interpreter.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.StateModel

open YulSemantics.EVM
open Challenge.YulProof.EvmState

/-- The value returned by the source helper `calldataByte`. -/
def calldataByteValue (st : EvmState) (off : U256) : U256 :=
  (wordFrom st.env.calldata off.toNat >>> 248) &&& 0xff

/-- EVM `ADDMOD`, stated directly on the source semantics' word type. -/
def addmodValue (a b modulus : U256) : U256 :=
  if modulus = 0 then 0
  else BitVec.ofNat 256 ((a.toNat + b.toNat) % modulus.toNat)

/-- EVM `MULMOD`, stated directly on the source semantics' word type. -/
def mulmodValue (a b modulus : U256) : U256 :=
  if modulus = 0 then 0
  else BitVec.ofNat 256 ((a.toNat * b.toNat) % modulus.toNat)

/-- The right-aligned modulus loaded by `modexpWord`. -/
def wordModulus (st : EvmState) (modulusSize modOff : U256) : U256 :=
  wordFrom st.env.calldata modOff.toNat >>> ((32 - modulusSize) * 8).toNat

/-- One Horner step of the streaming base reduction. -/
def baseStep (st : EvmState) (baseOff modulus : U256) (i : Nat)
    (base : U256) : U256 :=
  addmodValue (mulmodValue base 256 modulus)
    (calldataByteValue st (baseOff + BitVec.ofNat 256 i)) modulus

/-- State after the first `i` base bytes have been reduced. -/
def basePrefix (st : EvmState) (baseOff modulus : U256) : Nat → U256
  | 0 => 0
  | i + 1 => baseStep st baseOff modulus i (basePrefix st baseOff modulus i)

/-- One branchless square-and-multiply source step. -/
def bitStep (acc base modulus byte : U256) (j : Nat) : U256 :=
  let bit := (byte >>> (7 - BitVec.ofNat 256 j).toNat) &&& 1
  let square := mulmodValue acc acc modulus
  let product := mulmodValue square base modulus
  let mask := 0 - bit
  square ^^^ ((square ^^^ product) &&& mask)

/-- State after the first `j` bits of one exponent byte. -/
def bitPrefix (base modulus byte : U256) : Nat → U256 → U256
  | 0, acc => acc
  | j + 1, acc => bitStep (bitPrefix base modulus byte j acc) base modulus byte j

/-- One complete exponent-byte step. -/
def exponentStep (st : EvmState) (expOff base modulus : U256) (i : Nat)
    (acc : U256) : U256 :=
  let byte := calldataByteValue st (expOff + BitVec.ofNat 256 i)
  bitPrefix base modulus byte 8 acc

/-- State after the first `i` exponent bytes. -/
def exponentPrefix (st : EvmState) (expOff base modulus : U256) : Nat → U256 → U256
  | 0, acc => acc
  | i + 1, acc =>
      exponentStep st expOff base modulus i
        (exponentPrefix st expOff base modulus i acc)

/-- The accumulator with which the exponent loop starts. -/
def initialAccumulator (modulus : U256) : U256 :=
  if modulus = 0 then 0 else 1 % modulus

/-- The exact state after the word-path `mstore`. -/
def wordStoredState (st : EvmState) (modulusSize acc : U256) : EvmState :=
  storeWordAt st 0x1800 (acc <<< ((32 - modulusSize) * 8).toNat)

/-- The exact state after the word-path `return`. -/
def wordReturnedState (st : EvmState) (modulusSize acc : U256) : EvmState :=
  let stored := wordStoredState st modulusSize acc
  { touchMemory stored 0x1800 modulusSize.toNat with
    halted := some (.ret, readBytes stored.memory 0x1800 modulusSize.toNat) }

/-- The exact state of the zero-modulus early return (no preceding store). -/
def zeroModulusReturnedState (st : EvmState) (modulusSize : U256) : EvmState :=
  { touchMemory st 0x1800 modulusSize.toNat with
    halted := some (.ret, readBytes st.memory 0x1800 modulusSize.toNat) }

end Challenge.Modexp.Reference.Proofs.Yul.StateModel
