import Challenge.Sha256.Reference.Proofs.Bytecode.Schedule
import Challenge.Sha256.Reference.Proofs.Bytecode.BigSigma
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
/-!
# Direct execution of the reference SHA-256 compression routine

This file starts the bytecode-local proof of `compress`.  Its public states
make the internal calling convention explicit, so the eventual round invariant
can be reused by proofs for independently optimized participant bytecode.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Compression

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem wordOfNatZero : UInt256.ofNat 0 = 0 := by decide
@[simp] private theorem wordStructZero : ({ val := 0 } : UInt256) = 0 := by decide

private theorem wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def entryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨435, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨436, .push ⟨2, by decide⟩ (UInt256.ofNat 621), by rfl, by decide⟩,
   ⟨437, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨438, .push ⟨2, by decide⟩ (UInt256.ofNat 446), by rfl, by decide⟩,
   ⟨439, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def copyAndLoopStartPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨440, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨441, .push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨442, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨443, .push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨444, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨445, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

def conditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨446, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨447, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨448, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨449, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨450, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨451, .push ⟨2, by decide⟩ (UInt256.ofNat 935), by rfl, by decide⟩,
   ⟨452, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def setupWPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨453, .push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨454, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨455, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨456, .push ⟨2, by decide⟩ (UInt256.ofNat 661), by rfl, by decide⟩,
   ⟨457, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨458, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨459, .push ⟨2, by decide⟩ (UInt256.ofNat 279), by rfl, by decide⟩,
   ⟨460, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupKPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨461, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨462, .push ⟨2, by decide⟩ (UInt256.ofNat 671), by rfl, by decide⟩,
   ⟨463, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨464, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨465, .push ⟨2, by decide⟩ (UInt256.ofNat 257), by rfl, by decide⟩,
   ⟨466, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupH6Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨467, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨468, .push ⟨2, by decide⟩ (UInt256.ofNat 703), by rfl, by decide⟩,
   ⟨469, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨470, .push ⟨2, by decide⟩ (UInt256.ofNat 686), by rfl, by decide⟩,
   ⟨471, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨472, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨473, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨474, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupH5Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨475, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨476, .push ⟨2, by decide⟩ (UInt256.ofNat 697), by rfl, by decide⟩,
   ⟨477, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨478, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨479, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨480, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupChPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨481, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨482, .op (.Dup ⟨7, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨483, .push ⟨2, by decide⟩ (UInt256.ofNat 212), by rfl, by decide⟩,
   ⟨484, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupBigSigma1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨485, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨486, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨487, .push ⟨2, by decide⟩ (UInt256.ofNat 714), by rfl, by decide⟩,
   ⟨488, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨489, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨490, .push ⟨2, by decide⟩ (UInt256.ofNat 163), by rfl, by decide⟩,
   ⟨491, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupH7Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨492, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨493, .push ⟨2, by decide⟩ (UInt256.ofNat 725), by rfl, by decide⟩,
   ⟨494, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨495, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨496, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨497, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishT1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨498, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨499, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨500, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨501, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨502, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def setupT2H2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨503, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨504, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨505, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨506, .push ⟨2, by decide⟩ (UInt256.ofNat 770), by rfl, by decide⟩,
   ⟨507, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨508, .push ⟨2, by decide⟩ (UInt256.ofNat 753), by rfl, by decide⟩,
   ⟨509, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨510, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨511, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨512, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupT2H1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨513, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨514, .push ⟨2, by decide⟩ (UInt256.ofNat 764), by rfl, by decide⟩,
   ⟨515, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨516, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨517, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨518, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupMajPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨519, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨520, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨521, .push ⟨2, by decide⟩ (UInt256.ofNat 233), by rfl, by decide⟩,
   ⟨522, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupBigSigma0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨523, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨524, .push ⟨2, by decide⟩ (UInt256.ofNat 780), by rfl, by decide⟩,
   ⟨525, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨526, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨527, .push ⟨2, by decide⟩ (UInt256.ofNat 114), by rfl, by decide⟩,
   ⟨528, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishT2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨529, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨530, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨531, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def shift76Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨532, .push ⟨2, by decide⟩ (UInt256.ofNat 803), by rfl, by decide⟩,
   ⟨533, .push ⟨2, by decide⟩ (UInt256.ofNat 796), by rfl, by decide⟩,
   ⟨534, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨535, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨536, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨537, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def store7Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨538, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨539, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨540, .push ⟨2, by decide⟩ (UInt256.ofNat 338), by rfl, by decide⟩,
   ⟨541, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def shift65Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨542, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨543, .push ⟨2, by decide⟩ (UInt256.ofNat 824), by rfl, by decide⟩,
   ⟨544, .push ⟨2, by decide⟩ (UInt256.ofNat 817), by rfl, by decide⟩,
   ⟨545, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨546, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨547, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨548, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def store6Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨549, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨550, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨551, .push ⟨2, by decide⟩ (UInt256.ofNat 338), by rfl, by decide⟩,
   ⟨552, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def storeEPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨553, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨554, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨555, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨556, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def setupH3ForH4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨557, .push ⟨2, by decide⟩ (UInt256.ofNat 858), by rfl, by decide⟩,
   ⟨558, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨559, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨560, .push ⟨2, by decide⟩ (UInt256.ofNat 849), by rfl, by decide⟩,
   ⟨561, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨562, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨563, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨564, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def storeH4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨565, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨566, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨567, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨568, .push ⟨1, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨569, .push ⟨2, by decide⟩ (UInt256.ofNat 338), by rfl, by decide⟩,
   ⟨570, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def shift32Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨571, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨572, .push ⟨2, by decide⟩ (UInt256.ofNat 879), by rfl, by decide⟩,
   ⟨573, .push ⟨2, by decide⟩ (UInt256.ofNat 872), by rfl, by decide⟩,
   ⟨574, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨575, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨576, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨577, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def store3Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨578, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨579, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨580, .push ⟨2, by decide⟩ (UInt256.ofNat 338), by rfl, by decide⟩,
   ⟨581, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def shift21Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨582, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨583, .push ⟨2, by decide⟩ (UInt256.ofNat 900), by rfl, by decide⟩,
   ⟨584, .push ⟨2, by decide⟩ (UInt256.ofNat 893), by rfl, by decide⟩,
   ⟨585, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨586, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨587, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨588, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def store2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨589, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨590, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨591, .push ⟨2, by decide⟩ (UInt256.ofNat 338), by rfl, by decide⟩,
   ⟨592, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishRoundPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨593, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨594, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨595, .push ⟨2, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨596, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨597, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨598, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨599, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨600, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨601, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨602, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨603, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨604, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨605, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨606, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨607, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨608, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨609, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨610, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨611, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨612, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨613, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨614, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨615, .push ⟨2, by decide⟩ (UInt256.ofNat 633), by rfl, by decide⟩,
   ⟨616, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def roundsExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  conditionPath ++
  [⟨617, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨618, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨619, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

def foldConditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨620, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨621, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨622, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨623, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨624, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨625, .push ⟨2, by decide⟩ (UInt256.ofNat 993), by rfl, by decide⟩,
   ⟨626, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def foldSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨627, .push ⟨2, by decide⟩ (UInt256.ofNat 982), by rfl, by decide⟩,
   ⟨628, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨629, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨630, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨631, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨632, .push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨633, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨634, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨635, .push ⟨2, by decide⟩ (UInt256.ofNat 974), by rfl, by decide⟩,
   ⟨636, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨637, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨638, .push ⟨2, by decide⟩ (UInt256.ofNat 318), by rfl, by decide⟩,
   ⟨639, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def foldStorePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨640, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨641, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨642, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨643, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨644, .push ⟨2, by decide⟩ (UInt256.ofNat 338), by rfl, by decide⟩,
   ⟨645, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def foldIncrementPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨646, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨647, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨648, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨649, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨650, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨651, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨652, .push ⟨2, by decide⟩ (UInt256.ofNat 938), by rfl, by decide⟩,
   ⟨653, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def foldExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  foldConditionPath ++
  [⟨654, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨655, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨656, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨657, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def compressEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 612
    stack := [msgOff, returnDest] ++ rest }

def callSchedule (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  Schedule.scheduleEntry s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest)

def afterSchedule (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  Schedule.scheduleResult s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest)

def copyHashState (s : State) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (MachineState.readPadded s.memory 288 256) 544
    activeWords := s.activeWordsAfterUInt256_2 544 256 288 256 }

def roundAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 633
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def afterCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 643
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def hValue (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory
    (Accessors.slotOffset 288 (UInt256.ofNat i))

def wValue (s : State) (j : Nat) : UInt256 :=
  MachineState.readWord s.memory
    (Accessors.slotOffset 800 (UInt256.ofNat j))

def kValue (s : State) (j : Nat) : UInt256 :=
  let offset := (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
    UInt256.ofNat 32).toNat
  UInt256.shiftRight (MachineState.readWord s.memory offset)
    (UInt256.ofNat 224)

def loadedE (s : State) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 416 32 }

def callW (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (loadedE s) 279 (UInt256.ofNat j) 0
    (UInt256.ofNat 661)
    ([UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotW (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (loadedE s) 800 (UInt256.ofNat j)
    (UInt256.ofNat 661)
    ([UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callK (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotW s msgOff returnDest rest j) 257
    (UInt256.ofNat j) 0 (UInt256.ofNat 671)
    ([wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotK (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.kAtReturned (gotW s msgOff returnDest rest j)
    (UInt256.ofNat j) (UInt256.ofNat 671)
    ([wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callH6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotK s msgOff returnDest rest j) 318
    (UInt256.ofNat 6) 0 (UInt256.ofNat 686)
    ([0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotH6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotK s msgOff returnDest rest j) 288
    (UInt256.ofNat 6) (UInt256.ofNat 686)
    ([0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callH5 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotH6 s msgOff returnDest rest j) 318
    (UInt256.ofNat 5) 0 (UInt256.ofNat 697)
    ([hValue s 6, 0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotH5 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotH6 s msgOff returnDest rest j) 288
    (UInt256.ofNat 5) (UInt256.ofNat 697)
    ([hValue s 6, 0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callCh (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.ternaryEntry (gotH5 s msgOff returnDest rest j) 212
    (hValue s 4) (hValue s 5) (hValue s 6) 0 (UInt256.ofNat 703)
    ([kValue s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotCh (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotH5 s msgOff returnDest rest j)
    (Word.evmCh (hValue s 4) (hValue s 5) (hValue s 6))
    (UInt256.ofNat 703)
    ([kValue s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def chPlusK (s : State) (j : Nat) : UInt256 :=
  Word.evmCh (hValue s 4) (hValue s 5) (hValue s 6) + kValue s j

def callBigSigma1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryEntry (gotCh s msgOff returnDest rest j) 163
    (hValue s 4) 0 (UInt256.ofNat 714)
    ([chPlusK s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotBigSigma1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotCh s msgOff returnDest rest j)
    (Word.evmBigSigma1 (hValue s 4)) (UInt256.ofNat 714)
    ([chPlusK s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callH7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotBigSigma1 s msgOff returnDest rest j) 318
    (UInt256.ofNat 7) 0 (UInt256.ofNat 725)
    ([Word.evmBigSigma1 (hValue s 4), chPlusK s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotH7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotBigSigma1 s msgOff returnDest rest j) 288
    (UInt256.ofNat 7) (UInt256.ofNat 725)
    ([Word.evmBigSigma1 (hValue s 4), chPlusK s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def t1 (s : State) (j : Nat) : UInt256 :=
  Challenge.EvmProof.Word.mask32
    (((hValue s 7 + Word.evmBigSigma1 (hValue s 4)) + chPlusK s j) +
      wValue s j)

def afterT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { gotH7 s msgOff returnDest rest j with
    pc := UInt256.ofNat 730
    stack := [t1 s j, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest }

def loadedA (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { afterT1 s msgOff returnDest rest j with
    activeWords := (afterT1 s msgOff returnDest rest j).activeWordsAfterUInt256
      288 32 }

def callT2H2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (loadedA s msgOff returnDest rest j) 318
    (UInt256.ofNat 2) 0 (UInt256.ofNat 753)
    ([0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff, hValue s 0,
      t1 s j, hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotT2H2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (loadedA s msgOff returnDest rest j) 288
    (UInt256.ofNat 2) (UInt256.ofNat 753)
    ([0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff, hValue s 0,
      t1 s j, hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callT2H1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotT2H2 s msgOff returnDest rest j) 318
    (UInt256.ofNat 1) 0 (UInt256.ofNat 764)
    ([hValue s 2, 0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff,
      hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotT2H1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotT2H2 s msgOff returnDest rest j) 288
    (UInt256.ofNat 1) (UInt256.ofNat 764)
    ([hValue s 2, 0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff,
      hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callMaj (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.ternaryEntry (gotT2H1 s msgOff returnDest rest j) 233
    (hValue s 0) (hValue s 1) (hValue s 2) 0 (UInt256.ofNat 770)
    ([UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotMaj (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotT2H1 s msgOff returnDest rest j)
    (Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2))
    (UInt256.ofNat 770)
    ([UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callBigSigma0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryEntry (gotMaj s msgOff returnDest rest j) 114
    (hValue s 0) 0 (UInt256.ofNat 780)
    ([Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2),
      UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotBigSigma0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotMaj s msgOff returnDest rest j)
    (Word.evmBigSigma0 (hValue s 0)) (UInt256.ofNat 780)
    ([Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2),
      UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def t2 (s : State) : UInt256 :=
  Challenge.EvmProof.Word.mask32
    (Word.evmBigSigma0 (hValue s 0) +
      Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2))

def afterT2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { gotBigSigma0 s msgOff returnDest rest j with
    pc := UInt256.ofNat 783
    stack := [t2 s, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest }

def roundContext (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : List UInt256 :=
  [t2 s, hValue s 0, t1 s j, hValue s 4,
    UInt256.ofNat j, msgOff, returnDest] ++ rest

def shiftLoadEntry (q : State) (src loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.loadEntry q 318 (UInt256.ofNat src) 0
    (UInt256.ofNat loadReturn) (UInt256.ofNat storeReturn :: context)

def shiftLoaded (q : State) (src loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.loadReturned q 288 (UInt256.ofNat src)
    (UInt256.ofNat loadReturn) (UInt256.ofNat storeReturn :: context)

def shiftStoreEntry (q : State) (src dest loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.storeEntry (shiftLoaded q src loadReturn storeReturn context) 338
    (UInt256.ofNat dest) (hValue q src) (UInt256.ofNat storeReturn) context

def shiftReturned (q : State) (src dest loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.storeReturned (shiftLoaded q src loadReturn storeReturn context)
    288 (UInt256.ofNat dest) (hValue q src) (UInt256.ofNat storeReturn) context

def afterShift7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterT2 s msgOff returnDest rest j) 6 7 796 803
    (roundContext s msgOff returnDest rest j)

def afterShift6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterShift7 s msgOff returnDest rest j) 5 6 817 824
    (roundContext s msgOff returnDest rest j)

def directStored (q : State) (offset : Nat) (value : UInt256)
    (nextPC : Nat) (context : List UInt256) : State :=
  { q with
    pc := UInt256.ofNat nextPC
    stack := context
    memory := MachineState.writeBytes q.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) offset
    activeWords := q.activeWordsAfterUInt256 offset 32 }

def afterStoreE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  directStored (afterShift6 s msgOff returnDest rest j) 448 (hValue s 4) 830
    (roundContext s msgOff returnDest rest j)

def h4LoadEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterStoreE s msgOff returnDest rest j
  Accessors.loadEntry q 318 (UInt256.ofNat 3) 0 (UInt256.ofNat 849)
    ([t1 s j, UInt256.ofNat 0xffffffff, UInt256.ofNat 858] ++
      roundContext s msgOff returnDest rest j)

def h4Loaded (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterStoreE s msgOff returnDest rest j
  Accessors.loadReturned q 288 (UInt256.ofNat 3) (UInt256.ofNat 849)
    ([t1 s j, UInt256.ofNat 0xffffffff, UInt256.ofNat 858] ++
      roundContext s msgOff returnDest rest j)

def newH4 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : UInt256 :=
  let q := afterStoreE s msgOff returnDest rest j
  Challenge.EvmProof.Word.mask32 (hValue q 3 + t1 s j)

def h4StoreEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.storeEntry (h4Loaded s msgOff returnDest rest j) 338
    (UInt256.ofNat 4) (newH4 s msgOff returnDest rest j)
    (UInt256.ofNat 858) (roundContext s msgOff returnDest rest j)

def afterStoreH4 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.storeReturned (h4Loaded s msgOff returnDest rest j) 288
    (UInt256.ofNat 4) (newH4 s msgOff returnDest rest j)
    (UInt256.ofNat 858) (roundContext s msgOff returnDest rest j)

def afterShift3 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterStoreH4 s msgOff returnDest rest j) 2 3 872 879
    (roundContext s msgOff returnDest rest j)

def afterShift2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterShift3 s msgOff returnDest rest j) 1 2 893 900
    (roundContext s msgOff returnDest rest j)

def afterStoreH1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterShift2 s msgOff returnDest rest j
  directStored q 320 (hValue s 0) 906 (roundContext s msgOff returnDest rest j)

def afterSecondIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterStoreH1 s msgOff returnDest rest j
  { q with
    pc := UInt256.ofNat 633
    stack := [UInt256.ofNat (j + 1), msgOff, returnDest] ++ rest
    memory := MachineState.writeBytes q.memory
      (Data.Bytes.natToBytesPadded
        (Challenge.EvmProof.Word.mask32 (t1 s j + t2 s)).toNat 32) 288
    activeWords := q.activeWordsAfterUInt256 288 32 }

def foldAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 938
    stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterFoldCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 948
    stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def savedOffset (i : Nat) : Nat :=
  (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
    UInt256.ofNat 544).toNat

def savedValue (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory (savedOffset i)

def loadedSaved (s : State) (i : Nat) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 (savedOffset i) 32 }

def foldCallH (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.loadEntry (loadedSaved s i) 318 (UInt256.ofNat i) 0
    (UInt256.ofNat 974)
    ([savedValue s i, UInt256.ofNat 0xffffffff, UInt256.ofNat 982,
      UInt256.ofNat i, msgOff, returnDest] ++ rest)

def foldGotH (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.loadReturned (loadedSaved s i) 288 (UInt256.ofNat i)
    (UInt256.ofNat 974)
    ([savedValue s i, UInt256.ofNat 0xffffffff, UInt256.ofNat 982,
      UInt256.ofNat i, msgOff, returnDest] ++ rest)

def foldedValue (s : State) (_msgOff _returnDest : UInt256)
    (_rest : List UInt256) (i : Nat) : UInt256 :=
  let q := loadedSaved s i
  Challenge.EvmProof.Word.mask32
    (hValue q i + savedValue s i)

def foldCallSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.storeEntry (foldGotH s msgOff returnDest rest i) 338
    (UInt256.ofNat i) (foldedValue s msgOff returnDest rest i)
    (UInt256.ofNat 982) ([UInt256.ofNat i, msgOff, returnDest] ++ rest)

def foldGotSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.storeReturned (foldGotH s msgOff returnDest rest i) 288
    (UInt256.ofNat i) (foldedValue s msgOff returnDest rest i)
    (UInt256.ofNat 982) ([UInt256.ofNat i, msgOff, returnDest] ++ rest)

def afterFoldIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { foldGotSet s msgOff returnDest rest i with
    pc := UInt256.ofNat 938
    stack := [UInt256.ofNat (i + 1), msgOff, returnDest] ++ rest }

def compressReturned (s : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest, stack := rest }

@[simp] private theorem entryPC (i : Nat) (hlo : 435 ≤ i) (hhi : i ≤ 452) :
    Artifact.referenceArtifact.instructionPC i =
      [612, 613, 616, 617, 620, 621, 622, 625, 628, 631, 632, 633,
       634, 636, 637, 638, 639, 642][i - 435]! := by
  interval_cases i <;> decide

@[simp] private theorem t1PC (i : Nat) (hlo : 453 ≤ i) (hhi : i ≤ 502) :
    Artifact.referenceArtifact.instructionPC i =
      [643, 646, 647, 652, 655, 656, 657, 660, 661, 662,
       665, 666, 667, 670, 671, 672, 675, 676, 679, 680,
       682, 685, 686, 687, 690, 691, 693, 696, 697, 698,
       699, 702, 703, 704, 705, 708, 709, 710, 713, 714,
       715, 718, 719, 721, 724, 725, 726, 727, 728, 729][i - 453]! := by
  interval_cases i <;> decide

@[simp] private theorem t2PC (i : Nat) (hlo : 503 ≤ i) (hhi : i ≤ 531) :
    Artifact.referenceArtifact.instructionPC i =
      [730, 733, 734, 739, 742, 743, 746, 747, 749, 752,
       753, 754, 757, 758, 760, 763, 764, 765, 766, 769,
       770, 771, 774, 775, 776, 779, 780, 781, 782][i - 503]! := by
  interval_cases i <;> decide

@[simp] private theorem updatePC (i : Nat) (hlo : 532 ≤ i) (hhi : i ≤ 616) :
    Artifact.referenceArtifact.instructionPC i =
      [783, 786, 789, 790, 792, 795, 796, 797, 799, 802,
       803, 804, 807, 810, 811, 813, 816, 817, 818, 820,
       823, 824, 825, 826, 829, 830, 833, 838, 839, 842,
       843, 845, 848, 849, 850, 851, 852, 854, 857, 858,
       859, 862, 865, 866, 868, 871, 872, 873, 875, 878,
       879, 880, 883, 886, 887, 889, 892, 893, 894, 896,
       899, 900, 901, 902, 905, 906, 911, 912, 913, 914,
       915, 916, 919, 920, 921, 922, 923, 924, 925, 927,
       928, 929, 930, 931, 934][i - 532]! := by
  interval_cases i <;> decide

@[simp] private theorem foldPC (i : Nat) (hlo : 617 ≤ i) (hhi : i ≤ 657) :
    Artifact.referenceArtifact.instructionPC i =
      [935, 936, 937, 938, 939, 941, 942, 943, 944, 947,
       948, 951, 956, 957, 959, 960, 963, 964, 965, 968,
       969, 970, 973, 974, 975, 976, 977, 978, 981, 982,
       983, 985, 986, 987, 988, 989, 992, 993, 994, 995,
       996][i - 617]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPath
      (compressEntry s msgOff returnDest rest) =
        some (callSchedule s msgOff returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 446 = true := by decide
  simp [entryPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressEntry, callSchedule, Schedule.scheduleEntry, List.exchange,
    hc2, hc3, hc4, hc5, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_copyAndLoopStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyAndLoopStartPath
      { s with pc := UInt256.ofNat 621
               stack := [msgOff, returnDest] ++ rest } =
        some (roundAt (copyHashState s) msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [copyAndLoopStartPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copyHashState, roundAt, hc2, hc3, hc4, hc5, hrun,
    State.activeWordsAfterUInt256_2]

set_option linter.unusedSimpArgs false in
theorem run_condition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (roundAt s msgOff returnDest rest j) =
        some (afterCondition s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat 64) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hjWord, Challenge.EvmProof.Word.word_toNat_ofNat, hj]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have htrue : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    roundAt, afterCondition, hc3, hc4, hc5, hrun, hlt, hzero, htrue]

set_option linter.unusedSimpArgs false in
theorem run_setupW (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupWPath
      (afterCondition s msgOff returnDest rest j) =
        some (callW s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hoff4 :
      ((UInt256.ofNat 4).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 416 := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 279 = true := by decide
  simp [setupWPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterCondition, callW, loadedE, hValue, Accessors.slotOffset,
    Accessors.loadEntry, List.exchange, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hoff4, hcode, hrun, hdest, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupK (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1014)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupKPath
      (gotW s msgOff returnDest rest j) =
        some (callK s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 257 = true := by decide
  simp [setupKPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotW, callK, wValue, hValue, loadedE, Accessors.loadReturned,
    Accessors.loadEntry, Accessors.slotOffset, List.exchange, hc3, hc4,
    hc5, hc6, hc7, hc8, hc9, hc10, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupH6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupH6Path
      (gotK s msgOff returnDest rest j) =
        some (callH6 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setupH6Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotK, callH6, gotW, loadedE, kValue, wValue, hValue,
    Accessors.kAtReturned, Accessors.loadReturned, Accessors.loadEntry,
    Accessors.slotOffset, List.exchange, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupH5 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1009)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupH5Path
      (gotH6 s msgOff returnDest rest j) =
        some (callH5 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setupH5Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotH6, callH5, gotK, gotW, loadedE, kValue, wValue, hValue,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.loadEntry,
    Accessors.slotOffset, List.exchange, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hc14, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupCh (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupChPath
      (gotH5 s msgOff returnDest rest j) =
        some (callCh s msgOff returnDest rest j) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 212 = true := by decide
  simp [setupChPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotH5, callCh, gotH6, gotK, gotW, loadedE, kValue, wValue, hValue,
    Functions.ternaryEntry, Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.slotOffset, List.exchange, hc10, hc11, hc12, hc13, hc14,
    hc15, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupBigSigma1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1009)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupBigSigma1Path
      (gotCh s msgOff returnDest rest j) =
        some (callBigSigma1 s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 163 = true := by decide
  simp [setupBigSigma1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotCh, callBigSigma1, gotH5, gotH6, gotK, gotW, loadedE,
    chPlusK, kValue, wValue, hValue, Functions.unaryReturned,
    Functions.unaryEntry, Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.slotOffset, List.exchange, hc7, hc8, hc9, hc10, hc11, hc12,
    hc13, hc14, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupH7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupH7Path
      (gotBigSigma1 s msgOff returnDest rest j) =
        some (callH7 s msgOff returnDest rest j) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setupH7Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotBigSigma1, callH7, gotCh, gotH5, gotH6, gotK, gotW, loadedE,
    chPlusK, kValue, wValue, hValue, Functions.unaryReturned,
    Accessors.loadEntry, Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.slotOffset, List.exchange, hc8, hc9, hc10, hc11, hc12,
    hc13, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_finishT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1011)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishT1Path
      (gotH7 s msgOff returnDest rest j) =
        some (afterT1 s msgOff returnDest rest j) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp [finishT1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotH7, afterT1, gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW,
    loadedE, t1, chPlusK, kValue, wValue, hValue,
    Challenge.EvmProof.Word.mask32, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.slotOffset,
    List.exchange, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hrun]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_setupT2H2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1007)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupT2H2Path
      (afterT1 s msgOff returnDest rest j) =
        some (callT2H2 s msgOff returnDest rest j) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  have hoff0 : Accessors.slotOffset 288 (UInt256.ofNat 0) = 288 := by decide
  have haddr0 :
      (UInt256.shiftLeft 0 (UInt256.ofNat 5) + UInt256.ofNat 288).toNat =
        288 := by decide
  simp [setupT2H2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterT1, loadedA, callT2H2, gotH7, gotBigSigma1, gotCh, gotH5,
    gotH6, gotK, gotW, loadedE, hValue, Accessors.slotOffset,
    Functions.unaryReturned, Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.loadEntry, List.exchange, hc5, hc6, hc7, hc8, hc9, hc10, hc11,
    hc12, hc13, hc14, hc15, hc16, hoff0, haddr0, hcode, hrun, hdest,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupT2H1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1007)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupT2H1Path
      (gotT2H2 s msgOff returnDest rest j) =
        some (callT2H1 s msgOff returnDest rest j) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [setupT2H1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotT2H2, callT2H1, loadedA, afterT1, gotH7, gotBigSigma1, gotCh,
    gotH5, gotH6, gotK, gotW, loadedE, hValue, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.loadEntry,
    Accessors.slotOffset, List.exchange, hc10, hc11, hc12, hc13, hc14,
    hc15, hc16, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupMaj (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1006)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupMajPath
      (gotT2H1 s msgOff returnDest rest j) =
        some (callMaj s msgOff returnDest rest j) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 233 = true := by decide
  simp [setupMajPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotT2H1, callMaj, gotT2H2, loadedA, afterT1, gotH7,
    gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW, loadedE, hValue,
    Functions.ternaryEntry, Functions.unaryReturned, Accessors.loadReturned,
    Accessors.kAtReturned, Accessors.slotOffset, List.exchange, hc11, hc12, hc13,
    hc14, hc15, hc16, hc17, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupBigSigma0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupBigSigma0Path
      (gotMaj s msgOff returnDest rest j) =
        some (callBigSigma0 s msgOff returnDest rest j) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 114 = true := by decide
  simp [setupBigSigma0Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotMaj, callBigSigma0, gotT2H1, gotT2H2, loadedA, afterT1, gotH7,
    gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW, loadedE, hValue,
    Functions.ternaryEntry, Functions.unaryEntry, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.slotOffset,
    List.exchange, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_finishT2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1010)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishT2Path
      (gotBigSigma0 s msgOff returnDest rest j) =
        some (afterT2 s msgOff returnDest rest j) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [finishT2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotBigSigma0, afterT2, gotMaj, gotT2H1, gotT2H2, loadedA, afterT1,
    gotH7, gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW, loadedE,
    t2, hValue, Challenge.EvmProof.Word.mask32, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.slotOffset,
    List.exchange, hc8, hc9, hc10, hc11, hc12, hc13, hrun]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_shiftLoad (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (q : State) (src loadReturn storeReturn startPC : Nat)
    (context : List UInt256)
    (hmatch :
      (path = shift76Path ∧ src = 6 ∧ loadReturn = 796 ∧
        storeReturn = 803 ∧ startPC = 783) ∨
      (path = shift65Path ∧ src = 5 ∧ loadReturn = 817 ∧
        storeReturn = 824 ∧ startPC = 803) ∨
      (path = shift32Path ∧ src = 2 ∧ loadReturn = 872 ∧
        storeReturn = 879 ∧ startPC = 858) ∨
      (path = shift21Path ∧ src = 1 ∧ loadReturn = 893 ∧
        storeReturn = 900 ∧ startPC = 879))
    (hpc : q.pc = UInt256.ofNat startPC) (hstack : q.stack = context)
    (hcap : context.length < 1016)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path q =
      some (shiftLoadEntry q src loadReturn storeReturn context) := by
  have hc0 : context.length < 1024 := by omega
  have hc1 : context.length + 1 < 1024 := by omega
  have hc2 : context.length + 2 < 1024 := by omega
  have hc3 : context.length + 3 < 1024 := by omega
  have hc4 : context.length + 4 < 1024 := by omega
  have hc5 : context.length + 5 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  rcases hmatch with h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  all_goals simp [shift76Path, shift65Path, shift32Path, shift21Path,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    shiftLoadEntry, Accessors.loadEntry, hpc, hstack, List.exchange, hc0,
    hc1, hc2, hc3, hc4, hc5,
    hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_shiftStore (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (q : State) (src dest loadReturn storeReturn : Nat)
    (context : List UInt256)
    (hmatch :
      (path = store7Path ∧ src = 6 ∧ dest = 7 ∧ loadReturn = 796 ∧
        storeReturn = 803) ∨
      (path = store6Path ∧ src = 5 ∧ dest = 6 ∧ loadReturn = 817 ∧
        storeReturn = 824) ∨
      (path = store3Path ∧ src = 2 ∧ dest = 3 ∧ loadReturn = 872 ∧
        storeReturn = 879) ∨
      (path = store2Path ∧ src = 1 ∧ dest = 2 ∧ loadReturn = 893 ∧
        storeReturn = 900))
    (hcap : context.length < 1018)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (shiftLoaded q src loadReturn storeReturn context) =
        some (shiftStoreEntry q src dest loadReturn storeReturn context) := by
  have hc1 : context.length + 1 < 1024 := by omega
  have hc2 : context.length + 2 < 1024 := by omega
  have hc3 : context.length + 3 < 1024 := by omega
  have hc4 : context.length + 4 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 338 = true := by decide
  rcases hmatch with h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  all_goals simp [store7Path, store6Path, store3Path, store2Path,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    shiftLoaded, shiftStoreEntry, hValue, Accessors.loadReturned,
    Accessors.storeEntry, List.exchange, hc1, hc2, hc3, hc4,
    hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_storeE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1013)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock storeEPath
      (afterShift6 s msgOff returnDest rest j) =
        some (afterStoreE s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have qT1run : (afterT1 s msgOff returnDest rest j).halt = .Running := by
    simpa [afterT1, gotH7, gotBigSigma1, gotCh, gotH5, gotH6, gotK,
      gotW, loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun
  have qB0run : (gotBigSigma0 s msgOff returnDest rest j).halt = .Running := by
    simpa [gotBigSigma0, gotMaj, gotT2H1, gotT2H2, loadedA,
      Functions.unaryReturned, Accessors.loadReturned] using qT1run
  simp [storeEPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterShift6, afterShift7, shiftReturned, shiftLoaded, afterT2,
    roundContext, afterStoreE, directStored, List.exchange,
    Accessors.storeReturned, Accessors.loadReturned,
    hc7, hc8, hc9, hc10, hrun, qB0run, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupH3ForH4 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1009)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupH3ForH4Path
      (afterStoreE s msgOff returnDest rest j) =
        some (h4LoadEntry s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  have qrun : (afterShift6 s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode :
      (afterShift6 s msgOff returnDest rest j).executionEnv.code =
        referenceBytecode := by
    change s.executionEnv.code = referenceBytecode
    exact hcode
  simp [setupH3ForH4Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    h4LoadEntry, afterStoreE, directStored, roundContext, Accessors.loadEntry,
    List.exchange, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    hcode, hrun, qrun, qcode, hdest]

set_option linter.unusedSimpArgs false in
theorem run_storeH4 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock storeH4Path
      (h4Loaded s msgOff returnDest rest j) =
        some (h4StoreEntry s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 338 = true := by decide
  let q := afterStoreE s msgOff returnDest rest j
  have qrun : q.halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode : q.executionEnv.code = referenceBytecode := by
    change s.executionEnv.code = referenceBytecode
    exact hcode
  change Challenge.EvmProof.Stepper.runLocatedBlock storeH4Path
      (Accessors.loadReturned q 288 (UInt256.ofNat 3) (UInt256.ofNat 849)
        ([t1 s j, UInt256.ofNat 0xffffffff, UInt256.ofNat 858] ++
          roundContext s msgOff returnDest rest j)) =
    some (Accessors.storeEntry
      (Accessors.loadReturned q 288 (UInt256.ofNat 3) (UInt256.ofNat 849)
        ([t1 s j, UInt256.ofNat 0xffffffff, UInt256.ofNat 858] ++
          roundContext s msgOff returnDest rest j))
      338 (UInt256.ofNat 4)
      (Challenge.EvmProof.Word.mask32 (hValue q 3 + t1 s j))
      (UInt256.ofNat 858) (roundContext s msgOff returnDest rest j))
  simp [storeH4Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hValue, roundContext,
    Challenge.EvmProof.Word.mask32, Accessors.loadReturned,
    Accessors.storeEntry, List.exchange, hc7, hc8, hc9, hc10, hc11,
    hc12, hc13, hcode, hrun, qrun, qcode, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_finishRound (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishRoundPath
      (afterShift2 s msgOff returnDest rest j) =
        some (afterSecondIteration s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hadd : UInt256.ofNat j + UInt256.ofNat 1 =
      UInt256.ofNat (j + 1) := Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 633 = true := by decide
  have qrun : (afterStoreE s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode :
      (afterStoreE s msgOff returnDest rest j).executionEnv.code =
        referenceBytecode := by
    change s.executionEnv.code = referenceBytecode
    exact hcode
  simp [finishRoundPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterShift2, afterShift3, shiftReturned, shiftLoaded, afterStoreH4,
    h4Loaded, afterStoreH1, directStored, afterSecondIteration, roundContext,
    Challenge.EvmProof.Word.mask32, Accessors.storeReturned,
    Accessors.loadReturned, List.exchange, hc3, hc4, hc5, hc6, hc7,
    hc8, hc9, hc10, hc11, hcode, hrun, qrun, qcode, hadd, hdest,
    State.activeWordsAfterUInt256]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_roundsExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock roundsExitPath
      (roundAt s msgOff returnDest rest 64) =
        some (foldAt s msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 64) (UInt256.ofNat 64) = 0 := by
    simp [UInt256.lt]
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest935 : Decode.isValidJumpDest referenceBytecode 935 = true := by decide
  simp [roundsExitPath, conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    roundAt, foldAt, List.exchange, hc2, hc3, hc4, hc5, hcode, hrun,
    hlt, hzero, htrue, hdest935]

set_option linter.unusedSimpArgs false in
theorem run_foldCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 8)
    (hcap : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldConditionPath
      (foldAt s msgOff returnDest rest i) =
        some (afterFoldCondition s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 8) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have htrue : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [foldConditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    foldAt, afterFoldCondition, hc3, hc4, hc5, hrun, hlt, hzero, htrue]

set_option linter.unusedSimpArgs false in
theorem run_foldSetup (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldSetupPath
      (afterFoldCondition s msgOff returnDest rest i) =
        some (foldCallH s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hoff : UInt256.ofNat 544 +
        UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
        UInt256.ofNat 544 := Challenge.EvmProof.Word.word_add_comm _ _
  have hdest : Decode.isValidJumpDest referenceBytecode 318 = true := by decide
  simp [foldSetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterFoldCondition, foldCallH, loadedSaved, savedValue, savedOffset,
    Accessors.loadEntry, List.exchange, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hoff, hcode, hrun, hdest,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_foldStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hcap : rest.length < 1012)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldStorePath
      (foldGotH s msgOff returnDest rest i) =
        some (foldCallSet s msgOff returnDest rest i) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 338 = true := by decide
  simp [foldStorePath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    foldGotH, foldCallSet, foldedValue, hValue, loadedSaved,
    Challenge.EvmProof.Word.mask32, Accessors.loadReturned,
    Accessors.storeEntry, List.exchange, hc4, hc5, hc6, hc7, hc8, hc9,
    hc10, hc11, hcode, hrun, hdest]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_foldIncrement (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 8)
    (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldIncrementPath
      (foldGotSet s msgOff returnDest rest i) =
        some (afterFoldIteration s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 =
      UInt256.ofNat (i + 1) := Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 938 = true := by decide
  simp [foldIncrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    foldGotSet, afterFoldIteration, foldGotH, loadedSaved,
    Accessors.storeReturned, Accessors.loadReturned, List.exchange,
    hc3, hc4, hc5, hcode, hrun, hadd, hdest]

set_option linter.unusedSimpArgs false in
theorem run_foldExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldExitPath
      (foldAt s msgOff returnDest rest 8) =
        some (compressReturned s returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 8) (UInt256.ofNat 8) = 0 := by
    simp [UInt256.lt]
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest993 : Decode.isValidJumpDest referenceBytecode 993 = true := by decide
  simp [foldExitPath, foldConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    foldAt, compressReturned, List.exchange, hc1, hc2, hc3, hc4, hc5,
    hcode, hrun, hlt, hzero, htrue, hdest993, hreturn]

end Challenge.Sha256.Reference.Proofs.Bytecode.Compression
