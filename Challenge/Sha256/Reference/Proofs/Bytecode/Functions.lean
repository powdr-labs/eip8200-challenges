import Challenge.Sha256.Reference.Proofs.Bytecode.Accessors
import Challenge.Sha256.Reference.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Certified summaries for the reference SHA arithmetic functions

The Yul compiler lowers internal functions to jumps.  This file proves the
raw opcode paths for the SHA arithmetic helpers and exposes their ordinary
input/output behavior.  Callers can use these summaries without expanding the
function bodies again.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Functions

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

def rotrPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨2, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨4, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨5, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨7, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨8, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨9, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨10, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨11, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨12, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨13, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨14, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨15, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨16, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨17, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨18, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨19, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def unaryEntry (s : State) (entry : Nat) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entry
    stack := [x, output, returnDest] ++ rest }

def rotrEntry (s : State) (x : UInt256) (n : Nat)
    (output returnDest : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4
    stack := [x, UInt256.ofNat n, output, returnDest] ++ rest }

def unaryReturned (s : State) (value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := value :: rest }

@[simp] private theorem pc2 : Artifact.referenceArtifact.instructionPC 2 = 4 := by decide
@[simp] private theorem pc3 : Artifact.referenceArtifact.instructionPC 3 = 5 := by decide
@[simp] private theorem pc4 : Artifact.referenceArtifact.instructionPC 4 = 10 := by decide
@[simp] private theorem pc5 : Artifact.referenceArtifact.instructionPC 5 = 11 := by decide
@[simp] private theorem pc6 : Artifact.referenceArtifact.instructionPC 6 = 12 := by decide
@[simp] private theorem pc7 : Artifact.referenceArtifact.instructionPC 7 = 14 := by decide
@[simp] private theorem pc8 : Artifact.referenceArtifact.instructionPC 8 = 15 := by decide
@[simp] private theorem pc9 : Artifact.referenceArtifact.instructionPC 9 = 16 := by decide
@[simp] private theorem pc10 : Artifact.referenceArtifact.instructionPC 10 = 17 := by decide
@[simp] private theorem pc11 : Artifact.referenceArtifact.instructionPC 11 = 18 := by decide
@[simp] private theorem pc12 : Artifact.referenceArtifact.instructionPC 12 = 19 := by decide
@[simp] private theorem pc13 : Artifact.referenceArtifact.instructionPC 13 = 20 := by decide
@[simp] private theorem pc14 : Artifact.referenceArtifact.instructionPC 14 = 21 := by decide
@[simp] private theorem pc15 : Artifact.referenceArtifact.instructionPC 15 = 22 := by decide
@[simp] private theorem pc16 : Artifact.referenceArtifact.instructionPC 16 = 23 := by decide
@[simp] private theorem pc17 : Artifact.referenceArtifact.instructionPC 17 = 24 := by decide
@[simp] private theorem pc18 : Artifact.referenceArtifact.instructionPC 18 = 25 := by decide
@[simp] private theorem pc19 : Artifact.referenceArtifact.instructionPC 19 = 26 := by decide
@[simp] private theorem rotrNext4 : (UInt256.ofNat 4).succ = UInt256.ofNat 5 := by decide
@[simp] private theorem rotrNext5 : UInt256.ofNat 5 + UInt256.ofNat 5 = UInt256.ofNat 10 := by decide
@[simp] private theorem rotrNext10 : (UInt256.ofNat 10).succ = UInt256.ofNat 11 := by decide
@[simp] private theorem rotrNext11 : (UInt256.ofNat 11).succ = UInt256.ofNat 12 := by decide
@[simp] private theorem rotrNext12 : UInt256.ofNat 12 + UInt256.ofNat 2 = UInt256.ofNat 14 := by decide
@[simp] private theorem rotrNext14 : (UInt256.ofNat 14).succ = UInt256.ofNat 15 := by decide
@[simp] private theorem rotrNext15 : (UInt256.ofNat 15).succ = UInt256.ofNat 16 := by decide
@[simp] private theorem rotrNext16 : (UInt256.ofNat 16).succ = UInt256.ofNat 17 := by decide
@[simp] private theorem rotrNext17 : (UInt256.ofNat 17).succ = UInt256.ofNat 18 := by decide
@[simp] private theorem rotrNext18 : (UInt256.ofNat 18).succ = UInt256.ofNat 19 := by decide
@[simp] private theorem rotrNext19 : (UInt256.ofNat 19).succ = UInt256.ofNat 20 := by decide
@[simp] private theorem rotrNext20 : (UInt256.ofNat 20).succ = UInt256.ofNat 21 := by decide
@[simp] private theorem rotrNext21 : (UInt256.ofNat 21).succ = UInt256.ofNat 22 := by decide
@[simp] private theorem rotrNext22 : (UInt256.ofNat 22).succ = UInt256.ofNat 23 := by decide
@[simp] private theorem rotrNext23 : (UInt256.ofNat 23).succ = UInt256.ofNat 24 := by decide
@[simp] private theorem rotrNext24 : (UInt256.ofNat 24).succ = UInt256.ofNat 25 := by decide
@[simp] private theorem rotrNext25 : (UInt256.ofNat 25).succ = UInt256.ofNat 26 := by decide

set_option linter.unusedSimpArgs false in
theorem run_rotr (s : State) (x : UInt256) (n : Nat)
    (output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hn : n ≤ 32)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath
      (rotrEntry s x n output returnDest rest) =
        some (unaryReturned s (Word.evmRotr32 x n) returnDest rest) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hn (by norm_num : 32 < 2 ^ 256)
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [rotrPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry, unaryReturned, Word.evmRotr32, Challenge.EvmProof.Word.mask32,
    List.exchange, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hcode, hrun, hvalid,
    hsub]
  rfl

def gasSteps_rotr (s : State) (x : UInt256) (n : Nat)
    (output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hn : n ≤ 32)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (rotrEntry s x n output returnDest rest)
      (unaryReturned s (Word.evmRotr32 x n) returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rotrPath
  · exact hcode
  · exact hfork
  · exact run_rotr s x n output returnDest rest hcap hn hcode hrun hvalid
  · exact hrun
  · exact hnp

def chPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨143, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨144, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨145, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨146, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨147, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨148, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨149, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨150, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨151, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨152, .op (.Swap ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨153, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨154, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨155, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨156, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨157, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨158, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def majPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨162, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨163, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨164, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨165, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨166, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨167, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨168, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨169, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨170, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨171, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨172, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨173, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨174, .op (.Swap ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨175, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨176, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨177, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨178, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨180, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def ternaryEntry (s : State) (entry : Nat) (x y z output returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entry
    stack := [x, y, z, output, returnDest] ++ rest }

@[simp] private theorem chPCs (i : Nat) (hi : 143 ≤ i) (hii : i ≤ 158) :
    Artifact.referenceArtifact.instructionPC i = i + 69 := by
  interval_cases i <;> decide

@[simp] private theorem majPCs (i : Nat) (hi : 162 ≤ i) (hii : i ≤ 180) :
    Artifact.referenceArtifact.instructionPC i = i + 71 := by
  interval_cases i <;> decide

@[simp] private theorem nextSmallPC (i : Nat) (hi : 212 ≤ i) (hii : i ≤ 250) :
    (UInt256.ofNat i).succ = UInt256.ofNat (i + 1) := by
  exact Challenge.EvmProof.Word.succ_ofNat (by omega)

set_option linter.unusedSimpArgs false in
theorem run_ch (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock chPath
      (ternaryEntry s 212 x y z output returnDest rest) =
        some (unaryReturned s (Word.evmCh x y z) returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [chPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ternaryEntry, unaryReturned, Word.evmCh, List.exchange, hc1, hc2, hc3,
    hc4, hc5, hc6, hc7, hc8, hcode, hrun, hvalid]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_maj (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock majPath
      (ternaryEntry s 233 x y z output returnDest rest) =
        some (unaryReturned s (Word.evmMaj x y z) returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [majPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ternaryEntry, unaryReturned, Word.evmMaj, List.exchange, hc1, hc2, hc3,
    hc4, hc5, hc6, hc7, hc8, hc9, hcode, hrun, hvalid]
  rfl

def gasSteps_ch (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (ternaryEntry s 212 x y z output returnDest rest)
      (unaryReturned s (Word.evmCh x y z) returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka chPath
  · exact hcode
  · exact hfork
  · exact run_ch s x y z output returnDest rest hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_maj (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (ternaryEntry s 233 x y z output returnDest rest)
      (unaryReturned s (Word.evmMaj x y z) returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka majPath
  · exact hcode
  · exact hfork
  · exact run_maj s x y z output returnDest rest hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

def ssig0SetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨23, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨24, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨25, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨26, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨27, .push ⟨2, by decide⟩ (UInt256.ofNat 48), by rfl, by decide⟩,
   ⟨28, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨29, .push ⟨1, by decide⟩ (UInt256.ofNat 18), by rfl, by decide⟩,
   ⟨30, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨31, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨32, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def ssig0MiddlePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨33, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨34, .push ⟨2, by decide⟩ (UInt256.ofNat 60), by rfl, by decide⟩,
   ⟨35, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨36, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨37, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨38, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨39, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def ssig0FinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨40, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨41, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨42, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨43, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨44, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨45, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨46, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨47, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem ssig0PC (i : Nat) (hlo : 23 ≤ i) (hhi : i ≤ 47) :
    Artifact.referenceArtifact.instructionPC i =
      [32, 33, 34, 36, 37, 40, 41, 43, 44, 47,
       48, 49, 52, 53, 55, 56, 59, 60, 61, 62, 63, 64, 65, 66, 67][i - 23]! := by
  interval_cases i <;> decide

def ssig0AfterSetup (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  rotrEntry s x 18 0 (UInt256.ofNat 48)
    (UInt256.shiftRight x (UInt256.ofNat 3) :: x :: output :: returnDest :: rest)

def ssig0AfterFirstRotr (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  unaryReturned s (Word.evmRotr32 x 18) (UInt256.ofNat 48)
    (UInt256.shiftRight x (UInt256.ofNat 3) :: x :: output :: returnDest :: rest)

def ssig0AfterMiddle (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  rotrEntry s x 7 0 (UInt256.ofNat 60)
    (Word.evmRotr32 x 18 :: UInt256.shiftRight x (UInt256.ofNat 3) ::
      x :: output :: returnDest :: rest)

def ssig0AfterSecondRotr (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  unaryReturned s (Word.evmRotr32 x 7) (UInt256.ofNat 60)
    (Word.evmRotr32 x 18 :: UInt256.shiftRight x (UInt256.ofNat 3) ::
      x :: output :: returnDest :: rest)

set_option linter.unusedSimpArgs false in
theorem run_ssig0Setup (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1013)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ssig0SetupPath
      (unaryEntry s 32 x output returnDest rest) =
        some (ssig0AfterSetup s x output returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 4 = true := by decide
  simp [ssig0SetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    unaryEntry, ssig0AfterSetup, rotrEntry, List.exchange, hc1, hc2, hc3,
    hc4, hc5, hc6, hc7, hc8, hc9, hcode, hrun, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_ssig0Middle (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ssig0MiddlePath
      (ssig0AfterFirstRotr s x output returnDest rest) =
        some (ssig0AfterMiddle s x output returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 4 = true := by decide
  simp [ssig0MiddlePath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ssig0AfterFirstRotr, ssig0AfterMiddle, unaryReturned, rotrEntry,
    List.exchange, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10,
    hcode, hrun, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_ssig0Finish (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock ssig0FinishPath
      (ssig0AfterSecondRotr s x output returnDest rest) =
        some (unaryReturned s (Word.evmSmallSigma0 x) returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [ssig0FinishPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ssig0AfterSecondRotr, unaryReturned, Word.evmSmallSigma0, List.exchange,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcode, hrun, hvalid]
  rfl

def gasSteps_ssig0 (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (unaryEntry s 32 x output returnDest rest)
      (unaryReturned s (Word.evmSmallSigma0 x) returnDest rest) := by
  have gSetup : Challenge.EvmProof.GasSteps
      (unaryEntry s 32 x output returnDest rest)
      (ssig0AfterSetup s x output returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka ssig0SetupPath
    · exact hcode
    · exact hfork
    · exact run_ssig0Setup s x output returnDest rest (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gFirst := gasSteps_rotr s x 18 0 (UInt256.ofNat 48)
    (UInt256.shiftRight x (UInt256.ofNat 3) :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gMiddle : Challenge.EvmProof.GasSteps
      (ssig0AfterFirstRotr s x output returnDest rest)
      (ssig0AfterMiddle s x output returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka ssig0MiddlePath
    · exact hcode
    · exact hfork
    · exact run_ssig0Middle s x output returnDest rest (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gSecond := gasSteps_rotr s x 7 0 (UInt256.ofNat 60)
    (Word.evmRotr32 x 18 :: UInt256.shiftRight x (UInt256.ofNat 3) ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gFinish : Challenge.EvmProof.GasSteps
      (ssig0AfterSecondRotr s x output returnDest rest)
      (unaryReturned s (Word.evmSmallSigma0 x) returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka ssig0FinishPath
    · exact hcode
    · exact hfork
    · exact run_ssig0Finish s x output returnDest rest (by omega)
        hcode hrun hvalid
    · exact hrun
    · exact hnp
  exact gSetup.trans (gFirst.trans (gMiddle.trans (gSecond.trans gFinish)))

def ssig1SetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨51, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨52, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨53, .push ⟨1, by decide⟩ (UInt256.ofNat 10), by rfl, by decide⟩,
   ⟨54, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨55, .push ⟨2, by decide⟩ (UInt256.ofNat 89), by rfl, by decide⟩,
   ⟨56, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨57, .push ⟨1, by decide⟩ (UInt256.ofNat 19), by rfl, by decide⟩,
   ⟨58, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨59, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨60, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def ssig1MiddlePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨61, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨62, .push ⟨2, by decide⟩ (UInt256.ofNat 101), by rfl, by decide⟩,
   ⟨63, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨64, .push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨65, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨66, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨67, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def ssig1FinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨68, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨69, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨70, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨71, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨72, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨73, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨74, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨75, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem ssig1PC (i : Nat) (hlo : 51 ≤ i) (hhi : i ≤ 75) :
    Artifact.referenceArtifact.instructionPC i =
      [73, 74, 75, 77, 78, 81, 82, 84, 85, 88,
       89, 90, 93, 94, 96, 97, 100, 101, 102, 103, 104, 105, 106, 107, 108][i - 51]! := by
  interval_cases i <;> decide

def ssig1AfterSetup (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  rotrEntry s x 19 0 (UInt256.ofNat 89)
    (UInt256.shiftRight x (UInt256.ofNat 10) :: x :: output :: returnDest :: rest)

def ssig1AfterFirstRotr (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  unaryReturned s (Word.evmRotr32 x 19) (UInt256.ofNat 89)
    (UInt256.shiftRight x (UInt256.ofNat 10) :: x :: output :: returnDest :: rest)

def ssig1AfterMiddle (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  rotrEntry s x 17 0 (UInt256.ofNat 101)
    (Word.evmRotr32 x 19 :: UInt256.shiftRight x (UInt256.ofNat 10) ::
      x :: output :: returnDest :: rest)

def ssig1AfterSecondRotr (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) : State :=
  unaryReturned s (Word.evmRotr32 x 17) (UInt256.ofNat 101)
    (Word.evmRotr32 x 19 :: UInt256.shiftRight x (UInt256.ofNat 10) ::
      x :: output :: returnDest :: rest)

set_option linter.unusedSimpArgs false in
theorem run_ssig1Setup (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1013)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ssig1SetupPath
      (unaryEntry s 73 x output returnDest rest) =
        some (ssig1AfterSetup s x output returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 4 = true := by decide
  simp [ssig1SetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    unaryEntry, ssig1AfterSetup, rotrEntry, List.exchange, hc1, hc2, hc3,
    hc4, hc5, hc6, hc7, hc8, hc9, hcode, hrun, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_ssig1Middle (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ssig1MiddlePath
      (ssig1AfterFirstRotr s x output returnDest rest) =
        some (ssig1AfterMiddle s x output returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 4 = true := by decide
  simp [ssig1MiddlePath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ssig1AfterFirstRotr, ssig1AfterMiddle, unaryReturned, rotrEntry,
    List.exchange, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10,
    hcode, hrun, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_ssig1Finish (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock ssig1FinishPath
      (ssig1AfterSecondRotr s x output returnDest rest) =
        some (unaryReturned s (Word.evmSmallSigma1 x) returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [ssig1FinishPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ssig1AfterSecondRotr, unaryReturned, Word.evmSmallSigma1, List.exchange,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcode, hrun, hvalid]
  rfl

def gasSteps_ssig1 (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (unaryEntry s 73 x output returnDest rest)
      (unaryReturned s (Word.evmSmallSigma1 x) returnDest rest) := by
  have gSetup : Challenge.EvmProof.GasSteps
      (unaryEntry s 73 x output returnDest rest)
      (ssig1AfterSetup s x output returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka ssig1SetupPath
    · exact hcode
    · exact hfork
    · exact run_ssig1Setup s x output returnDest rest (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gFirst := gasSteps_rotr s x 19 0 (UInt256.ofNat 89)
    (UInt256.shiftRight x (UInt256.ofNat 10) :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gMiddle : Challenge.EvmProof.GasSteps
      (ssig1AfterFirstRotr s x output returnDest rest)
      (ssig1AfterMiddle s x output returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka ssig1MiddlePath
    · exact hcode
    · exact hfork
    · exact run_ssig1Middle s x output returnDest rest (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gSecond := gasSteps_rotr s x 17 0 (UInt256.ofNat 101)
    (Word.evmRotr32 x 19 :: UInt256.shiftRight x (UInt256.ofNat 10) ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gFinish : Challenge.EvmProof.GasSteps
      (ssig1AfterSecondRotr s x output returnDest rest)
      (unaryReturned s (Word.evmSmallSigma1 x) returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka ssig1FinishPath
    · exact hcode
    · exact hfork
    · exact run_ssig1Finish s x output returnDest rest (by omega)
        hcode hrun hvalid
    · exact hrun
    · exact hnp
  exact gSetup.trans (gFirst.trans (gMiddle.trans (gSecond.trans gFinish)))

end Challenge.Sha256.Reference.Proofs.Bytecode.Functions
