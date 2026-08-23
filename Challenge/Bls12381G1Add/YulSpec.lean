import Challenge.Bls12381G1Add.Spec
import Challenge.YulProof.Bytes
import Challenge.YulProof.ModexpDialect
import YulSemantics.Contract

set_option warningAsError true

/-!
# BLS12-381 G1ADD Yul challenge statement

`Correct` is the auditor-facing source obligation. It mentions the
mathematical G1ADD specification and source semantics only: no optimizer,
compiler, instruction list, assembly, or EVM bytecode appears here.
-/

namespace Challenge.Bls12381G1Add.Yul

open YulSemantics (Block RunContract)
open YulSemantics.EVM (Op HaltKind)
open Challenge.YulProof.Modexp

/-- Observable halt required for one calldata byte list. -/
def expected (calldata : List UInt8) : HaltKind × List UInt8 :=
  match Challenge.Bls12381G1Add.spec (ByteArray.mk calldata.toArray) with
  | some output => (.ret, output.toList)
  | none => (.invalid, [])

@[simp] theorem expected_toList (input : ByteArray) :
    expected input.toList =
      match Challenge.Bls12381G1Add.spec input with
      | some output => (.ret, output.toList)
      | none => (.invalid, []) := by
  simp [expected, Challenge.YulProof.Bytes.ofToList]

/-- **The Yul challenge.** From fresh memory and EVM-sized calldata, the
program must return the G1 sum or halt with `invalid` for malformed input.

The dialect permits only successful calls to Osaka MODEXP at `0x05`; in
particular, a candidate cannot call the native G1ADD precompile at `0x0b`.
The fixed MODEXP stipends used by the reference are part of its source proof,
not assumptions in this predicate. -/
def Correct (program : Block Op) : Prop :=
  RunContract (D := dialect) program
    (fun initial =>
      initial.memory = (fun _ => 0) ∧
      initial.halted = none ∧
      ∃ input : ByteArray,
        initial.env.calldata = input.toList ∧
        Challenge.Bls12381G1Add.CalldataFits input)
    (fun initial _ final outcome =>
      outcome = .halt ∧
      final.halted = some (expected initial.env.calldata))

end Challenge.Bls12381G1Add.Yul
