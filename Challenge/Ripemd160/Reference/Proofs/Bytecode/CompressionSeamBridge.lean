import Challenge.Ripemd160.Reference.Proofs.Bytecode.DirectCorrect
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.RoundTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Schedule

set_option warningAsError true

/-!
# Compression seam closure adapter

This file isolates the exact remaining block-compression obligation.  Unlike
`DirectCorrect.CompressionSeam`, `CompressionRun` carries the functional hash
invariant after *every* padded block.  Consequently its final-word field is a
theorem, not an additional hypothesis.

The committed `CompressionTrace` currently exposes schedule setup/copy and an
abstract left/right 80-round fold, but no executable theorem from
`compressEntry` through the right loop and final combination.  Thus the
uniform `blockTrace` field below cannot yet be constructed from its public
API without adding those missing paths.  Once such a theorem is exported,
`toCompressionSeam` closes the end-to-end functional seam directly.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionSeamBridge

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

/-- Mathematical chaining state after `n` padded blocks. -/
def hashAfter (input : ByteArray) (n : Nat) : Array UInt32 :=
  SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
    (Padding.paddedMessage input) 0 n

/-- The five EVM chaining slots agree with the mathematical state after
`n` blocks.  This is the invariant preserved by a concrete compressor. -/
def HashWordsAt (input : ByteArray) (n : Nat) (s : State) : Prop :=
  ∀ i : Fin 5, OutputTrace.hWord s i =
    Challenge.EvmProof.Word.ofUInt32 (hashAfter input n)[i]!

/-- A complete run of the compiled compressor over all padded blocks.

`blockTrace` is deliberately one uniform machine theorem rather than an
unrelated hypothesis at each call site.  `hashWords` records its functional
invariant at every iteration, so final digest words follow by specialization.
-/
structure CompressionRun (input : ByteArray) where
  states : Nat → State
  initial : DriverTrace.setupEntry (states 0) input = PaddingTrace.padReturned input
  code : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).executionEnv.code = referenceBytecode
  fork : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).fork = .Osaka
  running : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).halt = .Running
  noPrecompile : ∀ i, i ≤ DriverTrace.blockCount input →
    Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig (states i).executionEnv.fork
      (states i).executionEnv.codeAddr = false
  callStack : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).callStack = []
  blockTrace : ∀ i, i < DriverTrace.blockCount input →
    GasSteps (DriverTrace.compressEntry (states i) input i)
      (DriverTrace.compressReturned (states (i + 1)) input i)
  hashWords : ∀ i, i ≤ DriverTrace.blockCount input →
    HashWordsAt input i (states i)

theorem finalWords (run : CompressionRun input) (i : Fin 5) :
    OutputTrace.hWord (run.states (DriverTrace.blockCount input)) i =
      Challenge.EvmProof.Word.ofUInt32
        (SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
          (Padding.paddedMessage input) 0
          (DriverTrace.blockCount input))[i]! := by
  exact run.hashWords (DriverTrace.blockCount input) (by omega) i

/-- Forget the stronger per-iteration functional invariant and obtain the
single interface consumed by `DirectCorrect`. -/
def toCompressionSeam (run : CompressionRun input) :
    DirectCorrect.CompressionSeam input where
  states := run.states
  initial := run.initial
  code := run.code
  fork := run.fork
  running := run.running
  noPrecompile := run.noPrecompile
  callStack := run.callStack
  compress := run.blockTrace
  finalWords := finalWords run

@[simp] theorem toCompressionSeam_states (run : CompressionRun input) :
    (toCompressionSeam run).states = run.states := rfl

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionSeamBridge
