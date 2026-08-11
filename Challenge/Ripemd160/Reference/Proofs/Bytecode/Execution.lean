import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

private theorem wfOp {op : Operation}
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

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat pc }

def mainStart (input : ByteArray) : State := atPC input 0x03ef

def path_start : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨20, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨21, .push ⟨2, by decide⟩ (UInt256.ofNat 0x2e), by rfl, by decide⟩,
   ⟨22, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_2e : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨35, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨36, .push ⟨2, by decide⟩ (UInt256.ofNat 0x46), by rfl, by decide⟩,
   ⟨37, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_46 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨52, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨53, .push ⟨2, by decide⟩ (UInt256.ofNat 0x5a), by rfl, by decide⟩,
   ⟨54, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_5a : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨67, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨68, .push ⟨2, by decide⟩ (UInt256.ofNat 0x73), by rfl, by decide⟩,
   ⟨69, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_73 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨83, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨84, .push ⟨2, by decide⟩ (UInt256.ofNat 0x8e), by rfl, by decide⟩,
   ⟨85, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_8e : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨105, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨106, .push ⟨2, by decide⟩ (UInt256.ofNat 0x10f), by rfl, by decide⟩,
   ⟨107, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_10f : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨205, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨206, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b2), by rfl, by decide⟩,
   ⟨207, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b2 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨313, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨314, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1db), by rfl, by decide⟩,
   ⟨315, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1db : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨346, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, .push ⟨2, by decide⟩ (UInt256.ofNat 0x231), by rfl, by decide⟩,
   ⟨348, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_231 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨410, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨411, .push ⟨2, by decide⟩ (UInt256.ofNat 0x268), by rfl, by decide⟩,
   ⟨412, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_268 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨448, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨449, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3c1), by rfl, by decide⟩,
   ⟨450, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3c1 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨647, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨648, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), by rfl, by decide⟩,
   ⟨649, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3ee : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨682, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0) (atPC input 0x1b) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_start
      (atPC input 0) = some (atPC input 0x1b) := by
    simp [path_start, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  have g : Challenge.EvmProof.GasSteps (atPC input 0) (atPC input 0x1b) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka path_start
    · rfl
    · rfl
    · exact hrun
    · rfl
    · exact deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast g rfl rfl

def gasSteps_1b (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b) (atPC input 0x2e) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1b
      (atPC input 0x1b) = some (atPC input 0x2e) := by
    simp [path_1b, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_1b
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x2e) (atPC input 0x46) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2e
      (atPC input 0x2e) = some (atPC input 0x46) := by
    simp [path_2e, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_2e
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_46 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x46) (atPC input 0x5a) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_46
      (atPC input 0x46) = some (atPC input 0x5a) := by
    simp [path_46, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_46
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_5a (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x5a) (atPC input 0x73) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_5a
      (atPC input 0x5a) = some (atPC input 0x73) := by
    simp [path_5a, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_5a
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_73 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x73) (atPC input 0x8e) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_73
      (atPC input 0x73) = some (atPC input 0x8e) := by
    simp [path_73, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_73
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_8e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x8e) (atPC input 0x10f) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_8e
      (atPC input 0x8e) = some (atPC input 0x10f) := by
    simp [path_8e, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_8e
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_10f (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x10f) (atPC input 0x1b2) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_10f
      (atPC input 0x10f) = some (atPC input 0x1b2) := by
    simp [path_10f, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_10f
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_1b2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b2) (atPC input 0x1db) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1b2
      (atPC input 0x1b2) = some (atPC input 0x1db) := by
    simp [path_1b2, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_1b2
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_1db (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1db) (atPC input 0x231) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1db
      (atPC input 0x1db) = some (atPC input 0x231) := by
    simp [path_1db, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_1db
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_231 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x231) (atPC input 0x268) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_231
      (atPC input 0x231) = some (atPC input 0x268) := by
    simp [path_231, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_231
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_268 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x268) (atPC input 0x3c1) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_268
      (atPC input 0x268) = some (atPC input 0x3c1) := by
    simp [path_268, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_268
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_3c1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3c1) (atPC input 0x3ee) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3c1
      (atPC input 0x3c1) = some (atPC input 0x3ee) := by
    simp [path_3c1, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_3c1
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3ee) (mainStart input) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3ee
      (atPC input 0x3ee) = some (mainStart input) := by
    simp [path_3ee, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, mainStart, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_3ee
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_entry (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (mainStart input) :=
  (gasSteps_start input).trans <|
  (gasSteps_1b input).trans <|
  (gasSteps_2e input).trans <|
  (gasSteps_46 input).trans <|
  (gasSteps_5a input).trans <|
  (gasSteps_73 input).trans <|
  (gasSteps_8e input).trans <|
  (gasSteps_10f input).trans <|
  (gasSteps_1b2 input).trans <|
  (gasSteps_1db input).trans <|
  (gasSteps_231 input).trans <|
  (gasSteps_268 input).trans <|
  (gasSteps_3c1 input).trans <|
  gasSteps_3ee input

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution
