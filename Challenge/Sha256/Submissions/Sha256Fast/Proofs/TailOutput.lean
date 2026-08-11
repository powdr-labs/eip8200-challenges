import Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailCompression
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.GasTools
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.OutputBlock
import Challenge.Sha256.Reference.Proofs.Bytecode.DriverCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailOutput

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Word
open MemoryCorrect TailState

private noncomputable def outputTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock OutputBlock.outputPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace OutputBlock.outputPath 122
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

namespace Ref

abbrev packNat :=
  Challenge.Sha256.Reference.Proofs.Bytecode.DriverCorrect.packNat
abbrev packedBytes_eq :=
  Challenge.Sha256.Reference.Proofs.Bytecode.DriverCorrect.packedBytes_eq
abbrev directPackWord :=
  Challenge.Sha256.Reference.Proofs.Bytecode.DriverCorrect.directPackWord
abbrev packNat_lt :=
  Challenge.Sha256.Reference.Proofs.Bytecode.DriverCorrect.packNat_lt
abbrev emitDigest :=
  Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge.emitDigest

end Ref

private theorem lor8_reverse (x0 x1 x2 x3 x4 x5 x6 x7 : UInt256) :
    UInt256.lor x7 (UInt256.lor x6 (UInt256.lor x5 (UInt256.lor x4
      (UInt256.lor x3 (UInt256.lor x2 (UInt256.lor x1 x0)))))) =
    UInt256.lor (UInt256.lor (UInt256.lor x0 x1) (UInt256.lor x2 x3))
      (UInt256.lor (UInt256.lor x4 x5) (UInt256.lor x6 x7)) := by
  apply word_ext
  simp only [word_toNat_lor]
  ac_rfl

theorem outputBytes_eq_emitDigest (H : Array UInt32) :
    DriverBlocks.outputBytes H[0]! H[1]! H[2]! H[3]!
      H[4]! H[5]! H[6]! H[7]! = Ref.emitDigest H := by
  let candidate := UInt256.lor (ofUInt32 H[7]!)
    (UInt256.lor (UInt256.shiftLeft (ofUInt32 H[6]!) (UInt256.ofNat 32))
      (UInt256.lor (UInt256.shiftLeft (ofUInt32 H[5]!) (UInt256.ofNat 64))
        (UInt256.lor (UInt256.shiftLeft (ofUInt32 H[4]!) (UInt256.ofNat 96))
          (UInt256.lor (UInt256.shiftLeft (ofUInt32 H[3]!) (UInt256.ofNat 128))
            (UInt256.lor (UInt256.shiftLeft (ofUInt32 H[2]!) (UInt256.ofNat 160))
              (UInt256.lor (UInt256.shiftLeft (ofUInt32 H[1]!) (UInt256.ofNat 192))
                (UInt256.shiftLeft (ofUInt32 H[0]!) (UInt256.ofNat 224))))))))
  have hc : candidate = UInt256.ofNat
      (Ref.packNat H[0]! H[1]! H[2]! H[3]! H[4]! H[5]! H[6]! H[7]!) := by
    dsimp [candidate]
    rw [lor8_reverse,
      Ref.directPackWord H[0]! H[1]! H[2]! H[3]!
        H[4]! H[5]! H[6]! H[7]!]
  unfold DriverBlocks.outputBytes
  change Data.Bytes.natToBytesPadded candidate.toNat 32 = _
  rw [hc, word_toNat_ofNat,
    Nat.mod_eq_of_lt (Ref.packNat_lt H[0]! H[1]! H[2]! H[3]!
      H[4]! H[5]! H[6]! H[7]!), Ref.packedBytes_eq]
  rfl

noncomputable def gasSteps_output (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (finalResult s H off endWord rem n rest)
      (outputResult s H off endWord rem n rest) :=
  let q := finalResult s H off endWord rem n rest
  let F := finalHash s H off endWord rem n rest
  let hF := finalResult_hash s H off endWord rem n rest
  let hresult : runLocatedBlock OutputBlock.outputPath q =
      some (outputResult s H off endWord rem n rest) := by
    simpa [q, F, outputResult] using OutputBlock.run_output q
      off endWord rem n F[0]! F[1]! F[2]! F[3]!
      F[4]! F[5]! F[6]! F[7]! rest (by omega) rfl
      (by simpa [q] using hrun) rfl rfl
      (hF 0 (by omega)) (hF 1 (by omega)) (hF 2 (by omega))
      (hF 3 (by omega)) (hF 4 (by omega)) (hF 5 (by omega))
      (hF 6 (by omega)) (hF 7 (by omega))
  outputTrace (by simpa [q] using hcode) (by simpa [q] using hfork)
    hresult (by simpa [q] using hrun) (by simpa [q] using hnp) (by simp)

@[simp] theorem gasSteps_output_cost (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 985)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_output s H off endWord rem n rest hcap hcode hfork hrun hnp).cost =
      122 := rfl

@[simp] theorem outputResult_return (s : State) (H : Array UInt32)
    (off endWord rem n : UInt256) (rest : List UInt256) :
    (outputResult s H off endWord rem n rest).hReturn =
      Ref.emitDigest (finalHash s H off endWord rem n rest) := by
  simp [outputResult, outputBytes_eq_emitDigest]

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailOutput
