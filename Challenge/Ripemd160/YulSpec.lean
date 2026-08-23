import Challenge.Ripemd160.Spec
import Challenge.YulProof.Bytes
import Challenge.YulProof.ClosedEvmDialect
import YulSemantics.Contract

set_option warningAsError true

/-!
# Ethereum RIPEMD-160 Yul challenge statement

`Challenge.Ripemd160.Yul.Correct` is the source-level acceptance predicate for
a Yul implementation of RIPEMD-160. It is the Yul analogue of
`Challenge.Ripemd160.Correct`: this is the definition an auditor should read
and the proposition a source candidate should prove.

The predicate is deliberately independent of the reference implementation,
the optimizer, and the compiler. It uses the closed EVM source dialect, in
which external calls and contract creation are unavailable, so a candidate
cannot delegate the digest computation to the incumbent `0x03` precompile.
-/

namespace Challenge.Ripemd160.Yul

open YulSemantics (Block RunContract)
open YulSemantics.EVM (Op)
open Challenge.YulProof.ClosedEvm

/-- The RIPEMD-160 precompile result at the byte-list boundary exposed by Yul
semantics. -/
def result (calldata : List UInt8) : List UInt8 :=
  (Challenge.Ripemd160.spec (ByteArray.mk calldata.toArray)).toList

@[simp] theorem result_toList (input : ByteArray) :
    result input.toList = (Challenge.Ripemd160.spec input).toList := by
  simp [result, Challenge.YulProof.Bytes.ofToList]

/-- **The Yul challenge.** From fresh memory and realizable calldata, the
program must halt with `return` and expose exactly
`Challenge.Ripemd160.spec`.

The contract quantifies over every fresh source state carrying fitting
calldata and interprets the program in the closed EVM dialect. It therefore
depends on no chosen parser, compiler, optimizer, reference AST, or external
call implementation. -/
def Correct (program : Block Op) : Prop :=
  RunContract (D := dialect) program
    (fun initial =>
      initial.memory = (fun _ => 0) ∧
      initial.halted = none ∧
      ∃ input : ByteArray,
        initial.env.calldata = input.toList ∧ Challenge.Ripemd160.CalldataFits input)
    (fun initial _ final outcome =>
      outcome = .halt ∧
      final.halted = some (.ret, result initial.env.calldata))

end Challenge.Ripemd160.Yul
