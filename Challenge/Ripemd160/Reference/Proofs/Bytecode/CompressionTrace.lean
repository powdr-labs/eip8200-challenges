import Challenge.Ripemd160.Reference.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ScheduleCorrect
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Reference.Proofs.Bytecode.RoundTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Direct trace skeleton for RIPEMD-160 compression

This module pins the whole `compress` body (artifact indices 451--646) and
exposes its four compositional seams: schedule construction, the left line,
the right line, and the final cross-combination.  Calls to the schedule and
round helpers remain `GasSteps` parameters; their independent direct traces
can therefore be substituted without replaying this control-flow proof.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka

/-- The exact frozen artifact interval occupied by `compress`.  `runBlock`
resolves every index through `referenceArtifact`, so these lists cannot drift
from the compiled bytecode. -/
def compressionPath : List Nat := List.range' 451 196

def scheduleSetupPath : List Nat := [451, 452, 453, 454, 455]
def copyStatePath : List Nat := List.range' 456 13
def leftInitPath : List Nat := [469]
def leftTestPath : List Nat := List.range' 470 7
def leftRoundSetupPath : List Nat := List.range' 477 28
def leftIncrementPath : List Nat := List.range' 505 9
def leftExitPath : List Nat := List.range' 514 2
def rightInitPath : List Nat := [516]
def rightTestPath : List Nat := List.range' 517 7
def rightRoundSetupPath : List Nat := List.range' 524 30
def rightIncrementPath : List Nat := List.range' 554 9
def rightExitPath : List Nat := List.range' 563 2
def combinationPath : List Nat := List.range' 565 82

def scheduleSetupLocated : List Located :=
  [⟨451, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨452, .push ⟨2, by decide⟩ (UInt256.ofNat 630), by rfl, by decide⟩,
   ⟨453, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨454, .push ⟨2, by decide⟩ (UInt256.ofNat 566), by rfl, by decide⟩,
   ⟨455, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem scheduleSetupPC (j : Nat)
    (hlo : 451 ≤ j) (hhi : j ≤ 455) :
    Artifact.referenceArtifact.instructionPC j =
      [621, 622, 625, 626, 629][j - 451]! := by
  interval_cases j <;> rfl

def copyStateLocated : List Located :=
  [⟨456, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨457, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨458, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨459, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨460, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨461, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨462, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨463, .push ⟨2, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨464, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨465, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨466, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨467, .push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨468, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem copyStatePC (j : Nat)
    (hlo : 456 ≤ j) (hhi : j ≤ 468) :
    Artifact.referenceArtifact.instructionPC j =
      [630, 631, 633, 635, 637, 638, 640, 642, 645, 646, 648,
        650, 653][j - 456]! := by
  interval_cases j <;> rfl

def leftTestLocated : List Located :=
  [⟨470, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨471, .push ⟨1, by decide⟩ (UInt256.ofNat 80), by rfl, by decide⟩,
   ⟨472, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨473, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨474, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨475, .push ⟨2, by decide⟩ (UInt256.ofNat 726), by rfl, by decide⟩,
   ⟨476, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem leftTestPC (j : Nat)
    (hlo : 470 ≤ j) (hhi : j ≤ 476) :
    Artifact.referenceArtifact.instructionPC j =
      [655, 656, 658, 659, 660, 661, 664][j - 470]! := by
  interval_cases j <;> rfl

def leftIncrementLocated : List Located :=
  [⟨505, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨506, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨507, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨508, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨509, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨510, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨511, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨512, .push ⟨2, by decide⟩ (UInt256.ofNat 655), by rfl, by decide⟩,
   ⟨513, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def leftInitLocated : List Located :=
  [⟨469, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def leftRoundPrefixLocated : List Located :=
  [⟨477, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨478, .push ⟨1, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨479, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨480, .push ⟨2, by decide⟩ (UInt256.ofNat 714), by rfl, by decide⟩,
   ⟨481, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨482, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨483, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨484, .push ⟨2, by decide⟩ (UInt256.ofNat 1568), by rfl, by decide⟩,
   ⟨485, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨486, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨487, .push ⟨2, by decide⟩ (UInt256.ofNat 693), by rfl, by decide⟩,
   ⟨488, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨489, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨490, .push ⟨2, by decide⟩ (UInt256.ofNat 1376), by rfl, by decide⟩,
   ⟨491, .push ⟨2, by decide⟩ (UInt256.ofNat 120), by rfl, by decide⟩,
   ⟨492, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def leftRoundMiddleLocated : List Located :=
  [⟨493, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨494, .push ⟨2, by decide⟩ (UInt256.ofNat 706), by rfl, by decide⟩,
   ⟨495, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨496, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨497, .push ⟨2, by decide⟩ (UInt256.ofNat 1184), by rfl, by decide⟩,
   ⟨498, .push ⟨2, by decide⟩ (UInt256.ofNat 120), by rfl, by decide⟩,
   ⟨499, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def leftRoundSuffixLocated : List Located :=
  [⟨500, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨501, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨502, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨503, .push ⟨2, by decide⟩ (UInt256.ofNat 276), by rfl, by decide⟩,
   ⟨504, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem leftInitPC :
    Artifact.referenceArtifact.instructionPC 469 = 654 := by rfl

@[simp] private theorem leftRoundSetupPC (j : Nat)
    (hlo : 477 ≤ j) (hhi : j ≤ 504) :
    Artifact.referenceArtifact.instructionPC j =
      [665, 666, 668, 669, 672, 673, 675, 676, 679, 680, 681, 684,
        685, 686, 689, 692, 693, 694, 697, 698, 699, 702, 705, 706,
        707, 708, 710, 713][j - 477]! := by
  interval_cases j <;> rfl

@[simp] private theorem leftExitPC (j : Nat)
    (hlo : 514 ≤ j) (hhi : j ≤ 516) :
    Artifact.referenceArtifact.instructionPC j = [726, 727, 728][j - 514]! := by
  interval_cases j <;> rfl

def leftExitLocated : List Located :=
  [⟨514, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨515, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def rightInitLocated : List Located :=
  [⟨516, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def rightTestLocated : List Located :=
  [⟨517, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨518, .push ⟨1, by decide⟩ (UInt256.ofNat 80), by rfl, by decide⟩,
   ⟨519, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨520, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨521, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨522, .push ⟨2, by decide⟩ (UInt256.ofNat 804), by rfl, by decide⟩,
   ⟨523, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def rightRoundPrefixLocated : List Located :=
  [⟨524, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨525, .push ⟨1, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨526, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨527, .push ⟨2, by decide⟩ (UInt256.ofNat 792), by rfl, by decide⟩,
   ⟨528, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨529, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨530, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨531, .push ⟨2, by decide⟩ (UInt256.ofNat 1728), by rfl, by decide⟩,
   ⟨532, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨533, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨534, .push ⟨2, by decide⟩ (UInt256.ofNat 767), by rfl, by decide⟩,
   ⟨535, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨536, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨537, .push ⟨2, by decide⟩ (UInt256.ofNat 1472), by rfl, by decide⟩,
   ⟨538, .push ⟨2, by decide⟩ (UInt256.ofNat 120), by rfl, by decide⟩,
   ⟨539, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def rightRoundMiddleLocated : List Located :=
  [⟨540, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨541, .push ⟨2, by decide⟩ (UInt256.ofNat 780), by rfl, by decide⟩,
   ⟨542, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨543, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨544, .push ⟨2, by decide⟩ (UInt256.ofNat 1280), by rfl, by decide⟩,
   ⟨545, .push ⟨2, by decide⟩ (UInt256.ofNat 120), by rfl, by decide⟩,
   ⟨546, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def rightRoundSuffixLocated : List Located :=
  [⟨547, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨548, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨549, .push ⟨1, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨550, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨551, .push ⟨2, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨552, .push ⟨2, by decide⟩ (UInt256.ofNat 276), by rfl, by decide⟩,
   ⟨553, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def rightIncrementLocated : List Located :=
  [⟨554, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨555, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨556, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨557, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨558, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨559, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨560, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨561, .push ⟨2, by decide⟩ (UInt256.ofNat 729), by rfl, by decide⟩,
   ⟨562, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def rightExitLocated : List Located :=
  [⟨563, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨564, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def combinationLocated : List Located :=
  [⟨565, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨566, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨567, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨568, .push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨569, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨570, .push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨571, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨572, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨573, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨574, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨575, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨576, .push ⟨2, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨577, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨578, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨579, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨580, .push ⟨2, by decide⟩ (UInt256.ofNat 576), by rfl, by decide⟩,
   ⟨581, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨582, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨583, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨584, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨585, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨586, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨587, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨588, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨589, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨590, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨591, .push ⟨2, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨592, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨593, .push ⟨2, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨594, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨595, .push ⟨2, by decide⟩ (UInt256.ofNat 608), by rfl, by decide⟩,
   ⟨596, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨597, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨598, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨599, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨600, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨601, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨602, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨603, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨604, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨605, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨606, .push ⟨2, by decide⟩ (UInt256.ofNat 384), by rfl, by decide⟩,
   ⟨607, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨608, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨609, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨610, .push ⟨2, by decide⟩ (UInt256.ofNat 640), by rfl, by decide⟩,
   ⟨611, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨612, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨613, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨614, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨615, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨616, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨617, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨618, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨619, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨620, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨621, .push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨622, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨623, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨624, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨625, .push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨626, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨627, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨628, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨629, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨630, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨631, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨632, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨633, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨634, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨635, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨636, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨637, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨638, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨639, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨640, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨641, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨642, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨643, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨644, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨645, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨646, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem leftIncrementPC (j : Nat)
    (hlo : 505 ≤ j) (hhi : j ≤ 513) :
    Artifact.referenceArtifact.instructionPC j =
      [714, 715, 716, 718, 719, 720, 721, 722, 725][j - 505]! := by
  interval_cases j <;> rfl

def compressEntry (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 621
           stack := [messageOffset, returnDest] ++ rest }

/-- State at the independently verified schedule helper (PC `0x236`). -/
def scheduleEntry (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 566
           stack := [messageOffset, UInt256.ofNat 630,
             messageOffset, returnDest] ++ rest }

/-- Return point supplied to the schedule helper.  Its memory is intentionally
caller-parametric: `ScheduleCorrect` supplies the schedule-memory invariant. -/
def scheduleReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 630
           stack := [messageOffset, returnDest] ++ rest }

def copyRegion (s : State) (dest src size : Nat) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (MachineState.readPadded s.memory src size) dest
    activeWords := s.activeWordsAfterUInt256_2 dest size src size }

def copiedWorkingState (s : State) : State :=
  copyRegion (copyRegion (copyRegion s 192 32 160) 352 32 160) 512 32 160

def copiesReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  let t := copiedWorkingState s
  { t with pc := UInt256.ofNat 654
           stack := [messageOffset, returnDest] ++ rest }

def leftLoopAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 655
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def leftBodyAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 665
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

/-- The round helper returns one disposable Yul expression above the loop
index.  The concrete round trace determines `discard`; loop control does not. -/
def leftRoundReturned (s : State) (messageOffset returnDest discard : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 714
           stack := discard :: UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def roundIndex (i : Nat) : Nat := i / 16

def constantAt (s : State) (base : Nat) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory (base + roundIndex i * 32)

def afterConstantLoad (s : State) (base : Nat) (i : Nat) : State :=
  { s with activeWords := (s.activeWordsAfterUInt256
      (base + roundIndex i * 32) 32) }

def leftFirstReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  TableTrace.tableAtReturned (afterConstantLoad s 1568 i)
    (UInt256.ofNat 1376) (UInt256.ofNat i)
    (UInt256.ofNat 693)
    ([constantAt s 1568 i, UInt256.ofNat 714, UInt256.ofNat (roundIndex i),
      UInt256.ofNat i, messageOffset, returnDest] ++ rest)

def leftSecondReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let q := leftFirstReturned s messageOffset returnDest rest i
  TableTrace.tableAtReturned q (UInt256.ofNat 1184) (UInt256.ofNat i)
    (UInt256.ofNat 706)
    ([TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i),
      constantAt s 1568 i, UInt256.ofNat 714,
      UInt256.ofNat (roundIndex i), UInt256.ofNat i,
      messageOffset, returnDest] ++ rest)

def leftRoundState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let q1 := leftFirstReturned s messageOffset returnDest rest i
  let q := leftSecondReturned s messageOffset returnDest rest i
  RoundTrace.roundReturned q (UInt256.ofNat 192) (roundIndex i)
    (TableTrace.tableValue q1 (UInt256.ofNat 1184) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
    (constantAt s 1568 i) (UInt256.ofNat 714)
    (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
      messageOffset :: returnDest :: rest)

set_option linter.unusedSimpArgs false in
theorem run_leftInit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftInitLocated
      (copiesReturned s messageOffset returnDest rest) =
        some (leftLoopAt (copiedWorkingState s) messageOffset returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [leftInitLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copiesReturned, leftLoopAt, copiedWorkingState, copyRegion, hrun, hc2]

set_option linter.unusedSimpArgs false in
theorem run_leftRoundPrefix (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1010) (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftRoundPrefixLocated
      (leftBodyAt s messageOffset returnDest rest i) =
      some (TableTrace.tableAtEntry (afterConstantLoad s 1568 i)
        (UInt256.ofNat 1376) (UInt256.ofNat i)
        (UInt256.ofNat 693)
        ([constantAt s 1568 i, UInt256.ofNat 714,
          UInt256.ofNat (roundIndex i), UInt256.ofNat i,
          messageOffset, returnDest] ++ rest)) := by
  have hshift : UInt256.shiftRight (UInt256.ofNat i) (UInt256.ofNat 4) =
      UInt256.ofNat (roundIndex i) := by
    rw [roundIndex, Challenge.EvmProof.Word.shiftRight_ofNat (by omega)
      (by decide)]
    simp [Nat.shiftRight_eq_div_pow]
  have haddr : UInt256.ofNat 1568 +
      UInt256.shiftLeft (UInt256.ofNat (roundIndex i)) (UInt256.ofNat 5) =
      UInt256.ofNat (1568 + roundIndex i * 32) := by
    have hj : roundIndex i < 5 := by unfold roundIndex; omega
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
  have haddrNat : (UInt256.ofNat 1568 +
      UInt256.shiftLeft (UInt256.ofNat (roundIndex i)) (UInt256.ofNat 5)).toNat =
      1568 + roundIndex i * 32 := by
    rw [haddr, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold roundIndex; omega)]
  have hsmall : 1568 + roundIndex i * 32 < 2 ^ 256 := by
    unfold roundIndex
    omega
  have hmod : (1568 + roundIndex i * 32) % 2 ^ 256 =
      1568 + roundIndex i * 32 := Nat.mod_eq_of_lt hsmall
  have hmodSize : (1568 + roundIndex i * 32) % UInt256.size =
      1568 + roundIndex i * 32 := by
    apply Nat.mod_eq_of_lt
    change 1568 + roundIndex i * 32 < 2 ^ 256
    exact hsmall
  have hmodLiteral : (1568 + roundIndex i * 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      1568 + roundIndex i * 32 := by
    apply Nat.mod_eq_of_lt
    change 1568 + roundIndex i * 32 < 2 ^ 256
    exact hsmall
  have hdest : Decode.isValidJumpDest referenceBytecode 120 = true := by decide
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 })
    [leftRoundPrefixLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      leftBodyAt, TableTrace.tableAtEntry, constantAt, afterConstantLoad,
      State.activeWordsAfterUInt256, hrun, hcode, hshift,
      haddr, haddrNat, hsmall, hmod, hmodSize, hmodLiteral,
      hdest, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_leftRoundMiddle (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftRoundMiddleLocated
      (leftFirstReturned s messageOffset returnDest rest i) =
      some (TableTrace.tableAtEntry
        (leftFirstReturned s messageOffset returnDest rest i)
        (UInt256.ofNat 1184) (UInt256.ofNat i) (UInt256.ofNat 706)
        ([TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i),
          constantAt s 1568 i, UInt256.ofNat 714,
          UInt256.ofNat (roundIndex i), UInt256.ofNat i,
          messageOffset, returnDest] ++ rest)) := by
  have hdest : Decode.isValidJumpDest referenceBytecode 120 = true := by decide
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 200000 })
    [leftRoundMiddleLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      leftFirstReturned, TableTrace.tableAtReturned, TableTrace.tableAtEntry,
      TableTrace.tableValue, afterConstantLoad, hrun, hcode, hdest, hcap,
      Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_leftRoundSuffix (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftRoundSuffixLocated
      (leftSecondReturned s messageOffset returnDest rest i) =
      some (RoundTrace.roundEntry
        (leftSecondReturned s messageOffset returnDest rest i)
        (UInt256.ofNat 192) (roundIndex i)
        (TableTrace.tableValue (leftFirstReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 1184) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
        (constantAt s 1568 i) (UInt256.ofNat 714)
        (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
          messageOffset :: returnDest :: rest)) := by
  have hdest : Decode.isValidJumpDest referenceBytecode 276 = true := by decide
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 200000 })
    [leftRoundSuffixLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      leftSecondReturned, leftFirstReturned, RoundTrace.roundEntry,
      TableTrace.tableAtReturned, TableTrace.tableValue, afterConstantLoad,
      hrun, hcode, hdest, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

def gasSteps_leftRoundSetup (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftBodyAt s messageOffset returnDest rest i)
      (leftRoundState s messageOffset returnDest rest i) := by
  let q0 := afterConstantLoad s 1568 i
  let tail1 := [constantAt s 1568 i, UInt256.ofNat 714,
    UInt256.ofNat (roundIndex i), UInt256.ofNat i,
    messageOffset, returnDest] ++ rest
  let q1 := leftFirstReturned s messageOffset returnDest rest i
  let tail2 := [TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i),
    constantAt s 1568 i, UInt256.ofNat 714, UInt256.ofNat (roundIndex i),
    UInt256.ofNat i, messageOffset, returnDest] ++ rest
  let q2 := leftSecondReturned s messageOffset returnDest rest i
  let roundTail := UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
    messageOffset :: returnDest :: rest
  have hq0code : q0.executionEnv.code = referenceBytecode := by
    simpa [q0, afterConstantLoad] using hcode
  have hq0fork : q0.fork = .Osaka := by
    simpa [q0, afterConstantLoad, State.fork] using hfork
  have hq0run : q0.halt = .Running := by simpa [q0, afterConstantLoad] using hrun
  have hq0np : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by simpa [q0, afterConstantLoad] using hnp
  have gp := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftRoundPrefixLocated
      (s := leftBodyAt s messageOffset returnDest rest i)
      hcode hfork
      (run_leftRoundPrefix s messageOffset returnDest rest i hi (by omega)
        hcode hrun) hrun hnp
  have gt1 := TableTrace.gasSteps_tableAt q0 (UInt256.ofNat 1376)
    (UInt256.ofNat i) (UInt256.ofNat 693) tail1 (by simp [tail1]; omega)
    hq0code hq0fork hq0run hq0np (by decide)
  have hq1code : q1.executionEnv.code = referenceBytecode := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hcode
  have hq1fork : q1.fork = .Osaka := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad, State.fork] using hfork
  have hq1run : q1.halt = .Running := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hrun
  have hq1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, leftFirstReturned, TableTrace.tableAtReturned,
      q0, afterConstantLoad] using hnp
  have gm := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftRoundMiddleLocated
      (s := q1)
      hq1code hq1fork
      (run_leftRoundMiddle s messageOffset returnDest rest i (by omega)
        hcode hrun) hq1run hq1np
  have gt2 := TableTrace.gasSteps_tableAt q1 (UInt256.ofNat 1184)
    (UInt256.ofNat i) (UInt256.ofNat 706) tail2 (by simp [tail2]; omega)
    hq1code hq1fork hq1run hq1np (by decide)
  have hq2code : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hcode
  have hq2fork : q2.fork = .Osaka := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad, State.fork] using hfork
  have hq2run : q2.halt = .Running := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hrun
  have hq2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, leftSecondReturned, q1, leftFirstReturned,
      TableTrace.tableAtReturned, afterConstantLoad] using hnp
  have gs := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftRoundSuffixLocated
      (s := q2)
      hq2code hq2fork
      (run_leftRoundSuffix s messageOffset returnDest rest i (by omega)
        hcode hrun) hq2run hq2np
  have gr := RoundTrace.gasSteps_round q2 (UInt256.ofNat 192) (roundIndex i)
    (by unfold roundIndex; omega)
    (TableTrace.tableValue q1 (UInt256.ofNat 1184) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
    (constantAt s 1568 i) (UInt256.ofNat 714) roundTail
    (by simp [roundTail]; omega) hq2code hq2fork hq2run hq2np (by decide)
  have hp' : Challenge.EvmProof.GasSteps
      (leftBodyAt s messageOffset returnDest rest i)
      (TableTrace.tableAtEntry q0 (UInt256.ofNat 1376) (UInt256.ofNat i)
        (UInt256.ofNat 693) tail1) :=
    Challenge.EvmProof.GasSteps.cast gp rfl (by simp [q0, tail1])
  have ht1' : Challenge.EvmProof.GasSteps
      (TableTrace.tableAtEntry q0 (UInt256.ofNat 1376) (UInt256.ofNat i)
        (UInt256.ofNat 693) tail1) q1 :=
    Challenge.EvmProof.GasSteps.cast gt1 rfl (by
      simp [q1, q0, tail1, leftFirstReturned])
  have hm' : Challenge.EvmProof.GasSteps q1
      (TableTrace.tableAtEntry q1 (UInt256.ofNat 1184) (UInt256.ofNat i)
        (UInt256.ofNat 706) tail2) :=
    Challenge.EvmProof.GasSteps.cast gm rfl (by simp [q1, tail2])
  have ht2' : Challenge.EvmProof.GasSteps
      (TableTrace.tableAtEntry q1 (UInt256.ofNat 1184) (UInt256.ofNat i)
        (UInt256.ofNat 706) tail2) q2 :=
    Challenge.EvmProof.GasSteps.cast gt2 rfl (by
      simp [q2, q1, tail2, leftSecondReturned])
  have hs' : Challenge.EvmProof.GasSteps q2
      (RoundTrace.roundEntry q2 (UInt256.ofNat 192) (roundIndex i)
        (TableTrace.tableValue q1 (UInt256.ofNat 1184) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
        (constantAt s 1568 i) (UInt256.ofNat 714) roundTail) :=
    Challenge.EvmProof.GasSteps.cast gs rfl (by simp [q2, q1, roundTail])
  have gr' : Challenge.EvmProof.GasSteps
      (RoundTrace.roundEntry q2 (UInt256.ofNat 192) (roundIndex i)
        (TableTrace.tableValue q1 (UInt256.ofNat 1184) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
        (constantAt s 1568 i) (UInt256.ofNat 714) roundTail)
      (leftRoundState s messageOffset returnDest rest i) :=
    Challenge.EvmProof.GasSteps.cast gr rfl (by
      simp [leftRoundState, q2, q1, roundTail])
  exact hp'.trans (ht1'.trans (hm'.trans (ht2'.trans (hs'.trans gr'))))

@[simp] theorem leftRoundState_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (leftRoundState s messageOffset returnDest rest i).executionEnv =
      s.executionEnv := by rfl

@[simp] theorem leftRoundState_fork (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (leftRoundState s messageOffset returnDest rest i).fork = s.fork := by
  rw [State.fork, leftRoundState_executionEnv]

@[simp] theorem leftRoundState_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (leftRoundState s messageOffset returnDest rest i).halt = s.halt := by rfl

@[simp] theorem leftRoundState_codeAddr (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (leftRoundState s messageOffset returnDest rest i).executionEnv.codeAddr =
      s.executionEnv.codeAddr := by
  rw [leftRoundState_executionEnv]

private theorem leftRoundState_atReturn (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    leftRoundState s messageOffset returnDest rest i =
      leftRoundReturned (leftRoundState s messageOffset returnDest rest i)
        messageOffset returnDest (UInt256.ofNat (roundIndex i)) rest i := by rfl

set_option linter.unusedSimpArgs false in
theorem run_scheduleSetup (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scheduleSetupLocated
      (compressEntry s messageOffset returnDest rest) =
        some (scheduleEntry s messageOffset returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 566 = true := by decide
  simp [scheduleSetupLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressEntry, scheduleEntry, hrun, hcode,
    hc2, hc3, hc4, hc5, hdest]

def gasSteps_scheduleSetup (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (compressEntry s messageOffset returnDest rest)
      (scheduleEntry s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scheduleSetupLocated
      (s := compressEntry s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_scheduleSetup s messageOffset returnDest rest hstack hcode hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_copyState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyStateLocated
      (scheduleReturned s messageOffset returnDest rest) =
        some (copiesReturned s messageOffset returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [copyStateLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scheduleReturned, copiesReturned, copiedWorkingState, copyRegion,
    hrun, hc2, hc3, hc4, hc5, State.activeWordsAfterUInt256_2]

def gasSteps_copyState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scheduleReturned s messageOffset returnDest rest)
      (copiesReturned s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka copyStateLocated
      (s := scheduleReturned s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_copyState s messageOffset returnDest rest hstack hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_leftTest_continue (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftTestLocated
      (leftLoopAt s messageOffset returnDest rest i) =
        some (leftBodyAt s messageOffset returnDest rest i) := by
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 80) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [leftTestLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    leftLoopAt, leftBodyAt, hrun, hlt, hzero, hfalse,
    hc3, hc4, hc5]

def gasSteps_leftTest_continue (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftLoopAt s messageOffset returnDest rest i)
      (leftBodyAt s messageOffset returnDest rest i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftTestLocated
      (s := leftLoopAt s messageOffset returnDest rest i)
  · exact hcode
  · exact hfork
  · exact run_leftTest_continue s messageOffset returnDest rest i hi hstack hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_leftIncrement (s : State) (messageOffset returnDest discard : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftIncrementLocated
      (leftRoundReturned s messageOffset returnDest discard rest i) =
        some (leftLoopAt s messageOffset returnDest rest (i + 1)) := by
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 655 = true := by decide
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [leftIncrementLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    leftRoundReturned, leftLoopAt, hrun, hcode, hadd, hdest,
    hc3, hc4, hc5, List.exchange]

def gasSteps_leftIncrement (s : State)
    (messageOffset returnDest discard : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftRoundReturned s messageOffset returnDest discard rest i)
      (leftLoopAt s messageOffset returnDest rest (i + 1)) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftIncrementLocated
      (s := leftRoundReturned s messageOffset returnDest discard rest i)
  · exact hcode
  · exact hfork
  · exact run_leftIncrement s messageOffset returnDest discard rest i hi
      hstack hcode hrun
  · exact hrun
  · exact hnp

/-- One complete left-line iteration, parameterized only by the table/round
helper seam.  This is the composition point consumed by the 80-round fold. -/
def gasSteps_leftIteration (s t : State)
    (messageOffset returnDest discard : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcodeS : s.executionEnv.code = referenceBytecode)
    (hcodeT : t.executionEnv.code = referenceBytecode)
    (hforkS : s.fork = .Osaka) (hforkT : t.fork = .Osaka)
    (hrunS : s.halt = .Running) (hrunT : t.halt = .Running)
    (hnpS : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hnpT : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false)
    (roundSeam : Challenge.EvmProof.GasSteps
      (leftBodyAt s messageOffset returnDest rest i)
      (leftRoundReturned t messageOffset returnDest discard rest i)) :
    Challenge.EvmProof.GasSteps
      (leftLoopAt s messageOffset returnDest rest i)
      (leftLoopAt t messageOffset returnDest rest (i + 1)) :=
  (gasSteps_leftTest_continue s messageOffset returnDest rest i hi hstack
    hcodeS hforkS hrunS hnpS).trans <|
    roundSeam.trans <|
      gasSteps_leftIncrement t messageOffset returnDest discard rest i hi
        hstack hcodeT hforkT hrunT hnpT

/-- Functional invariant paired with the bytecode loop index. -/
def LeftInvariant (word : Nat → UInt32) (initial : Compression.EvmWorking)
    (i : Nat) (current : Compression.EvmWorking) : Prop :=
  current = CompressionCorrect.evmLeftRounds word i initial

theorem leftInvariant_zero (word : Nat → UInt32)
    (initial : Compression.EvmWorking) :
    LeftInvariant word initial 0 initial := by
  rfl

theorem leftInvariant_step (word : Nat → UInt32)
    (initial current : Compression.EvmWorking) (i : Nat)
    (h : LeftInvariant word initial i current) :
    LeftInvariant word initial (i + 1)
      (CompressionCorrect.evmLeftStep word i current) := by
  subst current
  rfl

theorem leftInvariant_embedded (word : Nat → UInt32)
    (initial : Compression.Working) (i : Nat) (hi : i ≤ 80) :
    LeftInvariant word (Compression.embed initial) i
      (Compression.embed (CompressionCorrect.leftRounds word i initial)) := by
  unfold LeftInvariant
  symm
  exact CompressionCorrect.evmLeftRounds_embed word i initial hi

/-- The fold theorem makes the bytecode's literal 80-iteration bound explicit
while permitting each round trace to update memory. -/
def gasSteps_left80 (I : Nat → State)
    (iteration : ∀ i, i < 80 → Challenge.EvmProof.GasSteps (I i) (I (i + 1))) :
    Challenge.EvmProof.GasSteps (I 0) (I 80) :=
  Challenge.EvmProof.GasSteps.iterateBounded 80 iteration

def gasSteps_leftIterationConcrete (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftLoopAt s messageOffset returnDest rest i)
      (leftLoopAt (leftRoundState s messageOffset returnDest rest i)
        messageOffset returnDest rest (i + 1)) := by
  have gt := gasSteps_leftTest_continue s messageOffset returnDest rest i hi
    (by omega) hcode hfork hrun hnp
  have gr := gasSteps_leftRoundSetup s messageOffset returnDest rest i hi
    hstack hcode hfork hrun hnp
  let q := leftRoundState s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by
    simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gi := gasSteps_leftIncrement q messageOffset returnDest
    (UInt256.ofNat (roundIndex i)) rest i hi (by omega)
    hqcode hqfork hqrun hqnp
  have gr' : Challenge.EvmProof.GasSteps
      (leftBodyAt s messageOffset returnDest rest i)
      (leftRoundReturned q messageOffset returnDest
        (UInt256.ofNat (roundIndex i)) rest i) :=
    Challenge.EvmProof.GasSteps.cast gr rfl (by
      simpa [q] using leftRoundState_atReturn s messageOffset returnDest rest i)
  exact gt.trans (gr'.trans gi)

def leftStates (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => s
  | i + 1 => leftRoundState (leftStates s messageOffset returnDest rest i)
      messageOffset returnDest rest i

@[simp] theorem leftStates_zero (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : leftStates s messageOffset returnDest rest 0 = s := rfl

@[simp] theorem leftStates_succ (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) :
    leftStates s messageOffset returnDest rest (i + 1) =
      leftRoundState (leftStates s messageOffset returnDest rest i)
        messageOffset returnDest rest i := rfl

theorem leftStates_executionEnv (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) :
    (leftStates s messageOffset returnDest rest i).executionEnv =
      s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [leftStates, ih]

theorem leftStates_halt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) :
    (leftStates s messageOffset returnDest rest i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [leftStates, ih]

def gasSteps_left80Concrete (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftLoopAt s messageOffset returnDest rest 0)
      (leftLoopAt (leftStates s messageOffset returnDest rest 80)
        messageOffset returnDest rest 80) := by
  apply gasSteps_left80 (fun i =>
    leftLoopAt (leftStates s messageOffset returnDest rest i)
      messageOffset returnDest rest i)
  intro i hi
  let q := leftStates s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = referenceBytecode := by
    rw [leftStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, leftStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by rw [leftStates_halt]; exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, leftStates_executionEnv] using hnp
  simpa [q, leftStates] using
    gasSteps_leftIterationConcrete q messageOffset returnDest rest i hi hstack
      hqcode hqfork hqrun hqnp

def rightLoopAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 729
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def rightBodyAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 739
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def rightRoundReturned (s : State) (messageOffset returnDest discard : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 792
           stack := discard :: UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def leftExitCompared (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 726
           stack := UInt256.ofNat 80 :: messageOffset :: returnDest :: rest }

def leftExited (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 728
           stack := messageOffset :: returnDest :: rest }

set_option linter.unusedSimpArgs false in
theorem run_leftTest_exit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftTestLocated
      (leftLoopAt s messageOffset returnDest rest 80) =
        some (leftExitCompared s messageOffset returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 80) (UInt256.ofNat 80) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest : Decode.isValidJumpDest referenceBytecode 726 = true := by decide
  simp [leftTestLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    leftLoopAt, leftExitCompared, hrun, hcode, hlt, hzero, htrue, hdest,
    hc3, hc4, hc5]

def gasSteps_leftTest_exit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftLoopAt s messageOffset returnDest rest 80)
      (leftExitCompared s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftTestLocated
      (s := leftLoopAt s messageOffset returnDest rest 80)
  · exact hcode
  · exact hfork
  · exact run_leftTest_exit s messageOffset returnDest rest hstack hcode hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_leftExit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftExitLocated
      (leftExitCompared s messageOffset returnDest rest) =
        some (leftExited s messageOffset returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [leftExitLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    leftExitCompared, leftExited, hrun, hc3,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat]

def gasSteps_leftExit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftExitCompared s messageOffset returnDest rest)
      (leftExited s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftExitLocated
      (s := leftExitCompared s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_leftExit s messageOffset returnDest rest hstack hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_rightInit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rightInitLocated
      (leftExited s messageOffset returnDest rest) =
        some (rightLoopAt s messageOffset returnDest rest 0) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [rightInitLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    leftExited, rightLoopAt, hrun, hc2, hc3, Nat.add_assoc,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat]

def gasSteps_rightInit (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftExited s messageOffset returnDest rest)
      (rightLoopAt s messageOffset returnDest rest 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rightInitLocated
      (s := leftExited s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_rightInit s messageOffset returnDest rest hstack hrun
  · exact hrun
  · exact hnp

def scheduledState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  Schedule.loopState s messageOffset (UInt256.ofNat 630)
    (messageOffset :: returnDest :: rest) 16

def leftInitialState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  copiedWorkingState (scheduledState s messageOffset returnDest rest)

def leftFinalState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  leftStates (leftInitialState s messageOffset returnDest rest)
    messageOffset returnDest rest 80

/-- Concrete handoff from the compiled `compress` entry through schedule,
the three working-state copies, and all eighty left-line rounds.  The result
is exactly the right-loop head at index zero, ready for `CompressionRightTrace`.
-/
def gasSteps_compressToRight (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (compressEntry s messageOffset returnDest rest)
      (rightLoopAt (leftFinalState s messageOffset returnDest rest)
        messageOffset returnDest rest 0) := by
  have gsetup := gasSteps_scheduleSetup s messageOffset returnDest rest
    (by omega) hcode hfork hrun hnp
  let tail := messageOffset :: returnDest :: rest
  have gschedule := Schedule.gasSteps_schedule s messageOffset
    (UInt256.ofNat 630) tail (by simp [tail]; omega)
    hcode hfork hrun hnp (by decide)
  let q := scheduledState s messageOffset returnDest rest
  have hqcode : q.executionEnv.code = referenceBytecode := by
    simpa [q, scheduledState] using hcode
  have hqfork : q.fork = .Osaka := by
    simpa [q, scheduledState, State.fork] using hfork
  have hqrun : q.halt = .Running := by
    simpa [q, scheduledState] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, scheduledState] using hnp
  have gcopy := gasSteps_copyState q messageOffset returnDest rest (by omega)
    hqcode hqfork hqrun hqnp
  let q0 := leftInitialState s messageOffset returnDest rest
  have hq0code : q0.executionEnv.code = referenceBytecode := by
    simpa [q0, q, leftInitialState, copiedWorkingState, copyRegion] using hqcode
  have hq0fork : q0.fork = .Osaka := by
    simpa [q0, q, leftInitialState, copiedWorkingState, copyRegion, State.fork]
      using hqfork
  have hq0run : q0.halt = .Running := by
    simpa [q0, q, leftInitialState, copiedWorkingState, copyRegion] using hqrun
  have hq0np : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by
    simpa [q0, q, leftInitialState, copiedWorkingState, copyRegion] using hqnp
  have ginit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftInitLocated
      (s := copiesReturned q messageOffset returnDest rest)
      hqcode hqfork
      (run_leftInit q messageOffset returnDest rest (by omega) hqrun)
      hqrun hqnp
  have gleft := gasSteps_left80Concrete q0 messageOffset returnDest rest hstack
    hq0code hq0fork hq0run hq0np
  let q80 := leftFinalState s messageOffset returnDest rest
  have hq80code : q80.executionEnv.code = referenceBytecode := by
    simpa [q80, leftFinalState, q0, leftStates_executionEnv] using hq0code
  have hq80fork : q80.fork = .Osaka := by
    simpa [q80, q0, leftFinalState, State.fork] using hq0fork
  have hq80run : q80.halt = .Running := by
    simpa [q80, leftFinalState, q0, leftStates_halt] using hq0run
  have hq80np : Precompile.isPrecompileWithConfig q80.executionEnv.precompileConfig q80.executionEnv.fork
      q80.executionEnv.codeAddr = false := by
    simpa [q80, leftFinalState, q0, leftStates_executionEnv] using hq0np
  have gtest := gasSteps_leftTest_exit q80 messageOffset returnDest rest
    (by omega) hq80code hq80fork hq80run hq80np
  have gexit := gasSteps_leftExit q80 messageOffset returnDest rest
    (by omega) hq80code hq80fork hq80run hq80np
  have gright := gasSteps_rightInit q80 messageOffset returnDest rest
    (by omega) hq80code hq80fork hq80run hq80np
  have gschedule' : Challenge.EvmProof.GasSteps
      (scheduleEntry s messageOffset returnDest rest)
      (scheduleReturned q messageOffset returnDest rest) := by
    exact Challenge.EvmProof.GasSteps.cast gschedule
      (by simp [tail, scheduleEntry, Schedule.scheduleEntry])
      (by simp [tail, q, scheduledState, scheduleReturned,
        Schedule.scheduleReturned])
  have gcopy' : Challenge.EvmProof.GasSteps
      (scheduleReturned q messageOffset returnDest rest)
      (copiesReturned q messageOffset returnDest rest) := gcopy
  have ginit' : Challenge.EvmProof.GasSteps
      (copiesReturned q messageOffset returnDest rest)
      (leftLoopAt q0 messageOffset returnDest rest 0) := by
    exact Challenge.EvmProof.GasSteps.cast ginit rfl (by
      simp [q0, q, leftInitialState])
  have gleft' : Challenge.EvmProof.GasSteps
      (leftLoopAt q0 messageOffset returnDest rest 0)
      (leftLoopAt q80 messageOffset returnDest rest 80) := by
    exact Challenge.EvmProof.GasSteps.cast gleft rfl (by
      simp [q80, q0, leftFinalState])
  exact gsetup.trans (gschedule'.trans (gcopy'.trans (ginit'.trans
    (gleft'.trans (gtest.trans (gexit.trans gright))))))

/-- Right-line loop skeleton.  `iteration` is discharged by composing the
right condition, table/round seam, and increment paths pinned above. -/
def gasSteps_right80 (I : Nat → State)
    (iteration : ∀ i, i < 80 → Challenge.EvmProof.GasSteps (I i) (I (i + 1))) :
    Challenge.EvmProof.GasSteps (I 0) (I 80) :=
  Challenge.EvmProof.GasSteps.iterateBounded 80 iteration

def RightInvariant (word : Nat → UInt32) (initial : Compression.EvmWorking)
    (i : Nat) (current : Compression.EvmWorking) : Prop :=
  current = CompressionCorrect.evmRightRounds word i initial

theorem rightInvariant_zero (word : Nat → UInt32)
    (initial : Compression.EvmWorking) :
    RightInvariant word initial 0 initial := by
  rfl

theorem rightInvariant_step (word : Nat → UInt32)
    (initial current : Compression.EvmWorking) (i : Nat)
    (h : RightInvariant word initial i current) :
    RightInvariant word initial (i + 1)
      (CompressionCorrect.evmRightStep word i current) := by
  subst current
  rfl

theorem rightInvariant_embedded (word : Nat → UInt32)
    (initial : Compression.Working) (i : Nat) (hi : i ≤ 80) :
    RightInvariant word (Compression.embed initial) i
      (Compression.embed (CompressionCorrect.rightRounds word i initial)) := by
  unfold RightInvariant
  symm
  exact CompressionCorrect.evmRightRounds_embed word i initial hi

def wordAt (s : State) (address : Nat) : UInt256 :=
  MachineState.readWord s.memory address

def workingAt (s : State) (base : Nat) : Compression.EvmWorking :=
  { a := wordAt s base
    b := wordAt s (base + 32)
    c := wordAt s (base + 64)
    d := wordAt s (base + 96)
    e := wordAt s (base + 128) }

def savedHashAt512 (s : State) : Compression.EvmHashState :=
  { h0 := wordAt s 512
    h1 := wordAt s 544
    h2 := wordAt s 576
    h3 := wordAt s 608
    h4 := wordAt s 640 }

/-- Values computed by artifact indices 565--639.  The unusual store order
(`64,96,128,160,32`) is the in-place implementation of RIPEMD's cross-line
combination; the old chaining words are read from the saved copy at `0x200`. -/
def tailCombination (s : State) : Compression.EvmHashState :=
  Compression.evmCombine (savedHashAt512 s) (workingAt s 192) (workingAt s 352)

theorem tailCombination_embedded (h : Compression.HashState)
    (left right : Compression.Working) :
    Compression.evmCombine (Compression.embedHash h)
      (Compression.embed left) (Compression.embed right) =
        Compression.embedHash (Compression.combine h left right) :=
  Compression.evmCombine_embed h left right

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace
