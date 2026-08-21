import Challenge.Modexp.Spec
import Challenge.YulProof.Bytes
import Challenge.YulProof.ClosedEvmDialect
import YulSemantics.Contract

set_option warningAsError true

/-!
# Ethereum MODEXP Yul challenge statement

`Challenge.Modexp.Yul.Correct` is the source-level acceptance predicate for a
Yul implementation of MODEXP.  It is the Yul analogue of
`Challenge.Modexp.Correct`: this is the definition an auditor should read and
the proposition a source candidate should prove.

The predicate is deliberately independent of the reference implementation,
the optimizer, and the compiler.  Those layers may transport a proof of this
predicate to the bytecode challenge, but they are not part of the functional
specification.
-/

namespace Challenge.Modexp.Yul

open YulSemantics (Block RunContract)
open YulSemantics.EVM (Op)
open Challenge.YulProof.ClosedEvm

/-- The mathematical MODEXP result at the byte-list boundary exposed by Yul
semantics. -/
def result (calldata : List UInt8) : List UInt8 :=
  (Challenge.Modexp.spec (ByteArray.mk calldata.toArray)).toList

@[simp] theorem result_toList (input : ByteArray) :
    result input.toList = (Challenge.Modexp.spec input).toList := by
  simp [result, Challenge.YulProof.Bytes.ofToList]

/-- **The Yul challenge.** From fresh memory and valid MODEXP calldata, the
program must halt with `return` and expose exactly `Challenge.Modexp.spec`.

The contract quantifies over every fresh source state carrying valid calldata;
it therefore does not depend on any chosen parser, compiler, optimizer, or
reference AST. -/
def Correct (program : Block Op) : Prop :=
  RunContract (D := dialect) program
    (fun initial =>
      initial.memory = (fun _ => 0) ∧
      initial.halted = none ∧
      ∃ input : ByteArray,
        initial.env.calldata = input.toList ∧ Challenge.Modexp.ValidInput input)
    (fun initial _ final outcome =>
      outcome = .halt ∧
      final.halted = some (.ret, result initial.env.calldata))

end Challenge.Modexp.Yul
