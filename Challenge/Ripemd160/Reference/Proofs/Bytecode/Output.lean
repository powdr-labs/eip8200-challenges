import Challenge.Ripemd160.Reference.Proofs.Bytecode.OutputTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Certified RIPEMD-160 output blocks

This layer turns the executable summaries of the reference bytecode's output
tail into gas-parametric traces.  The generic certificate is intentionally
public: individual blocks, inner-loop iterations, and the five outer-loop
iterations can be joined with `GasSteps.trans` without replaying the opcode
proof.  The byte lemma below identifies the `MSTORE8` value with the byte used
by the RIPEMD-160 specification's `writeLE32` routine.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Output

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka

/-- Lift any successful certified output path to a uniform exact-gas trace. -/
def gasSteps_block (path : List Located) (s t : State)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path hcode hfork hresult hrun hnp

@[simp] theorem gasSteps_block_cost (path : List Located) (s t : State)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_block path s t hcode hfork hresult hrun hnp).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost path s := by
  rfl

/-- Exact-gas certificate for zeroing the 32-byte return window. -/
def gasSteps_prelude (s : State) (offset : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1022)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      { s with pc := UInt256.ofNat 0x64e, stack := offset :: rest }
      { OutputTrace.zeroOutput s with
        pc := UInt256.ofNat 0x654, stack := ⟨0⟩ :: rest } :=
  gasSteps_block OutputTrace.preludePath _ _ hcode hfork
    (OutputTrace.run_prelude s offset rest hcap hrun) hrun hnp

/-- Exact-gas certificate for one body pass of the four-byte writer loop. -/
def gasSteps_writeBody (s : State) (offset : Nat) (word : UInt256) (j : Nat)
    (ret : UInt256) (rest : List UInt256) (hj : j < 4)
    (hoff256 : offset + j < 2 ^ 256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      { s with
        pc := UInt256.ofNat 0x3d2
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: rest }
      { OutputTrace.writeByte s offset word j with
        pc := UInt256.ofNat 0x3c8
        stack := UInt256.ofNat (j + 1) :: UInt256.ofNat offset :: word :: ret :: rest } :=
  gasSteps_block OutputTrace.writeBodyPath _ _ hcode hfork
    (OutputTrace.run_writeBody s offset word j ret rest hj hoff256 hcap hcode hrun)
    hrun hnp

/-- The exact byte emitted by the Yul `writeLE32` loop. -/
def ripemdByte (w : UInt32) (j : Nat) : UInt8 :=
  ((w >>> UInt32.ofNat (8 * j)) &&& 0xff).toUInt8

/-- For each of the four byte indices, the EVM `SHR; AND 0xff; MSTORE8`
expression is the corresponding byte of RIPEMD-160's `writeLE32`. -/
theorem wordByte_ofUInt32 (w : UInt32) (j : Nat) (hj : j < 4) :
    OutputTrace.wordByte (Challenge.EvmProof.Word.ofUInt32 w) j =
      ripemdByte w j := by
  have hshift : 8 * j < 32 := by omega
  have hff : UInt256.ofNat 0xff =
      Challenge.EvmProof.Word.ofUInt32 (0xff : UInt32) := by decide
  have hand (x : UInt32) :
      UInt256.land (Challenge.EvmProof.Word.ofUInt32 x)
          (Challenge.EvmProof.Word.ofUInt32 (0xff : UInt32)) =
        Challenge.EvmProof.Word.ofUInt32 (x &&& (0xff : UInt32)) := by
    exact (Challenge.EvmProof.Word.ofUInt32_and x 0xff).symm
  unfold OutputTrace.wordByte ripemdByte
  rw [Challenge.EvmProof.Word.shiftRight_ofUInt32 w (8 * j) hshift, hff, hand]
  rw [Challenge.EvmProof.Word.ofUInt32_toNat,
    show 256 = 2 ^ 8 by norm_num, UInt8.ofNat_mod_size,
    UInt8.ofNat_uInt32ToNat]

/-- A certified writer iteration stores the corresponding specification byte. -/
theorem writeByte_ofUInt32 (s : State) (offset : Nat) (w : UInt32)
    (j : Nat) (hj : j < 4) :
    OutputTrace.writeByte s offset (Challenge.EvmProof.Word.ofUInt32 w) j =
      { s with
        memory := MachineState.writeBytes s.memory
          (ByteArray.mk #[ripemdByte w j]) (offset + j)
        activeWords := s.activeWordsAfterUInt256 (offset + j) 1 } := by
  simp [OutputTrace.writeByte, wordByte_ofUInt32 w j hj]

/-- If the five words in the reference state slots model RIPEMD-160's
`H[0..4]`, every byte consumed by the five writer calls is the matching
little-endian digest byte. -/
theorem hWordByte_of_model (s : State) (H : Array UInt32) (i : Fin 5)
    (j : Nat) (hj : j < 4)
    (hmodel : OutputTrace.hWord s i =
      Challenge.EvmProof.Word.ofUInt32 H[i]!) :
    OutputTrace.wordByte (OutputTrace.hWord s i) j =
      ripemdByte H[i]! j := by
  rw [hmodel]
  exact wordByte_ofUInt32 H[i]! j hj

/-- `RETURN(0, 32)` returns precisely the current 32-byte memory window. -/
def gasSteps_finish (s : State) (rest : List UInt256)
    (hcap : rest.length < 1022)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      { s with pc := UInt256.ofNat 0x681, stack := UInt256.ofNat 5 :: rest }
      { s with
        pc := UInt256.ofNat 0x686
        stack := rest
        halt := .Returned
        hReturn := MachineState.readPadded s.memory 0 32
        activeWords := s.activeWordsAfterUInt256 0 32 } :=
  gasSteps_block OutputTrace.finishPath _ _ hcode hfork
    (OutputTrace.run_finish s rest hcap hrun) hrun hnp

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Output
