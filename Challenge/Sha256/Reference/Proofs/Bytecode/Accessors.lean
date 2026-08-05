import Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Certified summaries for the reference memory accessors

The backend inlines the Yul accessors instead of compiling them to internal
jumps, so there is no `wAt`/`hAt`/`wSet`/`hSet` function body left to summarize
once: the address computation `PUSH1 5; SHL; PUSH2 base; ADD` followed by
`MLOAD` or `MSTORE` is spliced at each use.  There are eleven such sites, all
five instructions long, plus one seven-instruction round-constant read.

The summaries therefore describe a *site* rather than a call.  `slotOffset`,
and the shape of the loaded and stored states, are unchanged — which is what
keeps the consuming schedule and compression proofs talking about the same
memory model.  Gone are the `returnDest` parameter and the entry/return frame:
an inlined site neither pushes a return address nor jumps.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Accessors

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def slotOffset (base : Nat) (index : UInt256) : Nat :=
  (UInt256.shiftLeft index (UInt256.ofNat 5) + UInt256.ofNat base).toNat

/-- Entering an inlined accessor site: the slot index is on top of the stack,
because the instruction before the site duplicated it there. -/
def slotEntry (s : State) (index : Nat) (slot : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC index)
    stack := slot :: rest }

/-- Entering an inlined write site, which also needs the value. -/
def storeEntry (s : State) (index : Nat) (slot value : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC index)
    stack := slot :: value :: rest }

/-- After the five instructions of an inlined read. -/
def loadReturned (s : State) (index base : Nat) (slot : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC (index + 5))
    stack := MachineState.readWord s.memory (slotOffset base slot) :: rest
    activeWords := s.activeWordsAfterUInt256 (slotOffset base slot) 32 }

/-- After the five instructions of an inlined write. -/
def storeReturned (s : State) (index base : Nat) (slot value : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC (index + 5))
    stack := rest
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (slotOffset base slot)
    activeWords := s.activeWordsAfterUInt256 (slotOffset base slot) 32 }

/-- After the seven instructions of the inlined round-constant read. -/
def kAtReturned (s : State) (slot : UInt256) (rest : List UInt256) : State :=
  let offset := (UInt256.shiftLeft slot (UInt256.ofNat 2) + UInt256.ofNat 32).toNat
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 221)
    stack := UInt256.shiftRight (MachineState.readWord s.memory offset)
      (UInt256.ofNat 224) :: rest
    activeWords := s.activeWordsAfterUInt256 offset 32 }

@[simp] private theorem pc208 :
    Artifact.referenceArtifact.instructionPC 208 = 601 := by decide

@[simp] private theorem pc209 :
    Artifact.referenceArtifact.instructionPC 209 = 603 := by decide

@[simp] private theorem pc210 :
    Artifact.referenceArtifact.instructionPC 210 = 604 := by decide

@[simp] private theorem pc211 :
    Artifact.referenceArtifact.instructionPC 211 = 607 := by decide

@[simp] private theorem pc212 :
    Artifact.referenceArtifact.instructionPC 212 = 608 := by decide

@[simp] private theorem pc213 :
    Artifact.referenceArtifact.instructionPC 213 = 609 := by decide

@[simp] private theorem pc214 :
    Artifact.referenceArtifact.instructionPC 214 = 610 := by decide

@[simp] private theorem pc215 :
    Artifact.referenceArtifact.instructionPC 215 = 612 := by decide

@[simp] private theorem pc216 :
    Artifact.referenceArtifact.instructionPC 216 = 613 := by decide

@[simp] private theorem pc217 :
    Artifact.referenceArtifact.instructionPC 217 = 615 := by decide

@[simp] private theorem pc218 :
    Artifact.referenceArtifact.instructionPC 218 = 616 := by decide

@[simp] private theorem pc219 :
    Artifact.referenceArtifact.instructionPC 219 = 617 := by decide

@[simp] private theorem pc220 :
    Artifact.referenceArtifact.instructionPC 220 = 619 := by decide

@[simp] private theorem pc221 :
    Artifact.referenceArtifact.instructionPC 221 = 620 := by decide

@[simp] private theorem pc463 :
    Artifact.referenceArtifact.instructionPC 463 = 995 := by decide

@[simp] private theorem pc464 :
    Artifact.referenceArtifact.instructionPC 464 = 997 := by decide

@[simp] private theorem pc465 :
    Artifact.referenceArtifact.instructionPC 465 = 998 := by decide

@[simp] private theorem pc466 :
    Artifact.referenceArtifact.instructionPC 466 = 1001 := by decide

@[simp] private theorem pc467 :
    Artifact.referenceArtifact.instructionPC 467 = 1002 := by decide

@[simp] private theorem pc468 :
    Artifact.referenceArtifact.instructionPC 468 = 1003 := by decide

@[simp] private theorem pc472 :
    Artifact.referenceArtifact.instructionPC 472 = 1011 := by decide

@[simp] private theorem pc473 :
    Artifact.referenceArtifact.instructionPC 473 = 1013 := by decide

@[simp] private theorem pc474 :
    Artifact.referenceArtifact.instructionPC 474 = 1014 := by decide

@[simp] private theorem pc475 :
    Artifact.referenceArtifact.instructionPC 475 = 1017 := by decide

@[simp] private theorem pc476 :
    Artifact.referenceArtifact.instructionPC 476 = 1018 := by decide

@[simp] private theorem pc477 :
    Artifact.referenceArtifact.instructionPC 477 = 1019 := by decide

@[simp] private theorem pc517 :
    Artifact.referenceArtifact.instructionPC 517 = 1080 := by decide

@[simp] private theorem pc518 :
    Artifact.referenceArtifact.instructionPC 518 = 1082 := by decide

@[simp] private theorem pc519 :
    Artifact.referenceArtifact.instructionPC 519 = 1083 := by decide

@[simp] private theorem pc520 :
    Artifact.referenceArtifact.instructionPC 520 = 1086 := by decide

@[simp] private theorem pc521 :
    Artifact.referenceArtifact.instructionPC 521 = 1087 := by decide

@[simp] private theorem pc522 :
    Artifact.referenceArtifact.instructionPC 522 = 1088 := by decide

@[simp] private theorem pc547 :
    Artifact.referenceArtifact.instructionPC 547 = 1130 := by decide

@[simp] private theorem pc548 :
    Artifact.referenceArtifact.instructionPC 548 = 1132 := by decide

@[simp] private theorem pc549 :
    Artifact.referenceArtifact.instructionPC 549 = 1133 := by decide

@[simp] private theorem pc550 :
    Artifact.referenceArtifact.instructionPC 550 = 1136 := by decide

@[simp] private theorem pc551 :
    Artifact.referenceArtifact.instructionPC 551 = 1137 := by decide

@[simp] private theorem pc552 :
    Artifact.referenceArtifact.instructionPC 552 = 1138 := by decide

@[simp] private theorem pc555 :
    Artifact.referenceArtifact.instructionPC 555 = 1142 := by decide

@[simp] private theorem pc556 :
    Artifact.referenceArtifact.instructionPC 556 = 1144 := by decide

@[simp] private theorem pc557 :
    Artifact.referenceArtifact.instructionPC 557 = 1145 := by decide

@[simp] private theorem pc558 :
    Artifact.referenceArtifact.instructionPC 558 = 1148 := by decide

@[simp] private theorem pc559 :
    Artifact.referenceArtifact.instructionPC 559 = 1149 := by decide

@[simp] private theorem pc560 :
    Artifact.referenceArtifact.instructionPC 560 = 1150 := by decide

@[simp] private theorem pc595 :
    Artifact.referenceArtifact.instructionPC 595 = 1199 := by decide

@[simp] private theorem pc596 :
    Artifact.referenceArtifact.instructionPC 596 = 1201 := by decide

@[simp] private theorem pc597 :
    Artifact.referenceArtifact.instructionPC 597 = 1202 := by decide

@[simp] private theorem pc598 :
    Artifact.referenceArtifact.instructionPC 598 = 1205 := by decide

@[simp] private theorem pc599 :
    Artifact.referenceArtifact.instructionPC 599 = 1206 := by decide

@[simp] private theorem pc600 :
    Artifact.referenceArtifact.instructionPC 600 = 1207 := by decide

@[simp] private theorem pc603 :
    Artifact.referenceArtifact.instructionPC 603 = 1211 := by decide

@[simp] private theorem pc604 :
    Artifact.referenceArtifact.instructionPC 604 = 1213 := by decide

@[simp] private theorem pc605 :
    Artifact.referenceArtifact.instructionPC 605 = 1214 := by decide

@[simp] private theorem pc606 :
    Artifact.referenceArtifact.instructionPC 606 = 1217 := by decide

@[simp] private theorem pc607 :
    Artifact.referenceArtifact.instructionPC 607 = 1218 := by decide

@[simp] private theorem pc608 :
    Artifact.referenceArtifact.instructionPC 608 = 1219 := by decide

@[simp] private theorem pc913 :
    Artifact.referenceArtifact.instructionPC 913 = 1668 := by decide

@[simp] private theorem pc914 :
    Artifact.referenceArtifact.instructionPC 914 = 1670 := by decide

@[simp] private theorem pc915 :
    Artifact.referenceArtifact.instructionPC 915 = 1671 := by decide

@[simp] private theorem pc916 :
    Artifact.referenceArtifact.instructionPC 916 = 1674 := by decide

@[simp] private theorem pc917 :
    Artifact.referenceArtifact.instructionPC 917 = 1675 := by decide

@[simp] private theorem pc918 :
    Artifact.referenceArtifact.instructionPC 918 = 1676 := by decide

@[simp] private theorem pc920 :
    Artifact.referenceArtifact.instructionPC 920 = 1678 := by decide

@[simp] private theorem pc921 :
    Artifact.referenceArtifact.instructionPC 921 = 1680 := by decide

@[simp] private theorem pc922 :
    Artifact.referenceArtifact.instructionPC 922 = 1681 := by decide

@[simp] private theorem pc923 :
    Artifact.referenceArtifact.instructionPC 923 = 1684 := by decide

@[simp] private theorem pc924 :
    Artifact.referenceArtifact.instructionPC 924 = 1685 := by decide

@[simp] private theorem pc925 :
    Artifact.referenceArtifact.instructionPC 925 = 1686 := by decide

@[simp] private theorem pc928 :
    Artifact.referenceArtifact.instructionPC 928 = 1689 := by decide

@[simp] private theorem pc929 :
    Artifact.referenceArtifact.instructionPC 929 = 1691 := by decide

@[simp] private theorem pc930 :
    Artifact.referenceArtifact.instructionPC 930 = 1692 := by decide

@[simp] private theorem pc931 :
    Artifact.referenceArtifact.instructionPC 931 = 1695 := by decide

@[simp] private theorem pc932 :
    Artifact.referenceArtifact.instructionPC 932 = 1696 := by decide

@[simp] private theorem pc933 :
    Artifact.referenceArtifact.instructionPC 933 = 1697 := by decide

@[simp] private theorem next208 : UInt256.ofNat 601 + UInt256.ofNat 2 = UInt256.ofNat 603 := by decide
@[simp] private theorem next209 : (UInt256.ofNat 603).succ = UInt256.ofNat 604 := by decide
@[simp] private theorem next210 : UInt256.ofNat 604 + UInt256.ofNat 3 = UInt256.ofNat 607 := by decide
@[simp] private theorem next211 : (UInt256.ofNat 607).succ = UInt256.ofNat 608 := by decide
@[simp] private theorem next212 : (UInt256.ofNat 608).succ = UInt256.ofNat 609 := by decide
@[simp] private theorem next213 : (UInt256.ofNat 609).succ = UInt256.ofNat 610 := by decide
@[simp] private theorem next214 : UInt256.ofNat 610 + UInt256.ofNat 2 = UInt256.ofNat 612 := by decide
@[simp] private theorem next215 : (UInt256.ofNat 612).succ = UInt256.ofNat 613 := by decide
@[simp] private theorem next216 : UInt256.ofNat 613 + UInt256.ofNat 2 = UInt256.ofNat 615 := by decide
@[simp] private theorem next217 : (UInt256.ofNat 615).succ = UInt256.ofNat 616 := by decide
@[simp] private theorem next218 : (UInt256.ofNat 616).succ = UInt256.ofNat 617 := by decide
@[simp] private theorem next219 : UInt256.ofNat 617 + UInt256.ofNat 2 = UInt256.ofNat 619 := by decide
@[simp] private theorem next220 : (UInt256.ofNat 619).succ = UInt256.ofNat 620 := by decide
@[simp] private theorem next463 : UInt256.ofNat 995 + UInt256.ofNat 2 = UInt256.ofNat 997 := by decide
@[simp] private theorem next464 : (UInt256.ofNat 997).succ = UInt256.ofNat 998 := by decide
@[simp] private theorem next465 : UInt256.ofNat 998 + UInt256.ofNat 3 = UInt256.ofNat 1001 := by decide
@[simp] private theorem next466 : (UInt256.ofNat 1001).succ = UInt256.ofNat 1002 := by decide
@[simp] private theorem next467 : (UInt256.ofNat 1002).succ = UInt256.ofNat 1003 := by decide
@[simp] private theorem next472 : UInt256.ofNat 1011 + UInt256.ofNat 2 = UInt256.ofNat 1013 := by decide
@[simp] private theorem next473 : (UInt256.ofNat 1013).succ = UInt256.ofNat 1014 := by decide
@[simp] private theorem next474 : UInt256.ofNat 1014 + UInt256.ofNat 3 = UInt256.ofNat 1017 := by decide
@[simp] private theorem next475 : (UInt256.ofNat 1017).succ = UInt256.ofNat 1018 := by decide
@[simp] private theorem next476 : (UInt256.ofNat 1018).succ = UInt256.ofNat 1019 := by decide
@[simp] private theorem next517 : UInt256.ofNat 1080 + UInt256.ofNat 2 = UInt256.ofNat 1082 := by decide
@[simp] private theorem next518 : (UInt256.ofNat 1082).succ = UInt256.ofNat 1083 := by decide
@[simp] private theorem next519 : UInt256.ofNat 1083 + UInt256.ofNat 3 = UInt256.ofNat 1086 := by decide
@[simp] private theorem next520 : (UInt256.ofNat 1086).succ = UInt256.ofNat 1087 := by decide
@[simp] private theorem next521 : (UInt256.ofNat 1087).succ = UInt256.ofNat 1088 := by decide
@[simp] private theorem next547 : UInt256.ofNat 1130 + UInt256.ofNat 2 = UInt256.ofNat 1132 := by decide
@[simp] private theorem next548 : (UInt256.ofNat 1132).succ = UInt256.ofNat 1133 := by decide
@[simp] private theorem next549 : UInt256.ofNat 1133 + UInt256.ofNat 3 = UInt256.ofNat 1136 := by decide
@[simp] private theorem next550 : (UInt256.ofNat 1136).succ = UInt256.ofNat 1137 := by decide
@[simp] private theorem next551 : (UInt256.ofNat 1137).succ = UInt256.ofNat 1138 := by decide
@[simp] private theorem next555 : UInt256.ofNat 1142 + UInt256.ofNat 2 = UInt256.ofNat 1144 := by decide
@[simp] private theorem next556 : (UInt256.ofNat 1144).succ = UInt256.ofNat 1145 := by decide
@[simp] private theorem next557 : UInt256.ofNat 1145 + UInt256.ofNat 3 = UInt256.ofNat 1148 := by decide
@[simp] private theorem next558 : (UInt256.ofNat 1148).succ = UInt256.ofNat 1149 := by decide
@[simp] private theorem next559 : (UInt256.ofNat 1149).succ = UInt256.ofNat 1150 := by decide
@[simp] private theorem next595 : UInt256.ofNat 1199 + UInt256.ofNat 2 = UInt256.ofNat 1201 := by decide
@[simp] private theorem next596 : (UInt256.ofNat 1201).succ = UInt256.ofNat 1202 := by decide
@[simp] private theorem next597 : UInt256.ofNat 1202 + UInt256.ofNat 3 = UInt256.ofNat 1205 := by decide
@[simp] private theorem next598 : (UInt256.ofNat 1205).succ = UInt256.ofNat 1206 := by decide
@[simp] private theorem next599 : (UInt256.ofNat 1206).succ = UInt256.ofNat 1207 := by decide
@[simp] private theorem next603 : UInt256.ofNat 1211 + UInt256.ofNat 2 = UInt256.ofNat 1213 := by decide
@[simp] private theorem next604 : (UInt256.ofNat 1213).succ = UInt256.ofNat 1214 := by decide
@[simp] private theorem next605 : UInt256.ofNat 1214 + UInt256.ofNat 3 = UInt256.ofNat 1217 := by decide
@[simp] private theorem next606 : (UInt256.ofNat 1217).succ = UInt256.ofNat 1218 := by decide
@[simp] private theorem next607 : (UInt256.ofNat 1218).succ = UInt256.ofNat 1219 := by decide
@[simp] private theorem next913 : UInt256.ofNat 1668 + UInt256.ofNat 2 = UInt256.ofNat 1670 := by decide
@[simp] private theorem next914 : (UInt256.ofNat 1670).succ = UInt256.ofNat 1671 := by decide
@[simp] private theorem next915 : UInt256.ofNat 1671 + UInt256.ofNat 3 = UInt256.ofNat 1674 := by decide
@[simp] private theorem next916 : (UInt256.ofNat 1674).succ = UInt256.ofNat 1675 := by decide
@[simp] private theorem next917 : (UInt256.ofNat 1675).succ = UInt256.ofNat 1676 := by decide
@[simp] private theorem next920 : UInt256.ofNat 1678 + UInt256.ofNat 2 = UInt256.ofNat 1680 := by decide
@[simp] private theorem next921 : (UInt256.ofNat 1680).succ = UInt256.ofNat 1681 := by decide
@[simp] private theorem next922 : UInt256.ofNat 1681 + UInt256.ofNat 3 = UInt256.ofNat 1684 := by decide
@[simp] private theorem next923 : (UInt256.ofNat 1684).succ = UInt256.ofNat 1685 := by decide
@[simp] private theorem next924 : (UInt256.ofNat 1685).succ = UInt256.ofNat 1686 := by decide
@[simp] private theorem next928 : UInt256.ofNat 1689 + UInt256.ofNat 2 = UInt256.ofNat 1691 := by decide
@[simp] private theorem next929 : (UInt256.ofNat 1691).succ = UInt256.ofNat 1692 := by decide
@[simp] private theorem next930 : UInt256.ofNat 1692 + UInt256.ofNat 3 = UInt256.ofNat 1695 := by decide
@[simp] private theorem next931 : (UInt256.ofNat 1695).succ = UInt256.ofNat 1696 := by decide
@[simp] private theorem next932 : (UInt256.ofNat 1696).succ = UInt256.ofNat 1697 := by decide

/-- Inlined slot read at instruction 208, base `800`. -/
def loadPath208 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨208, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨209, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨210, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨211, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨212, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot read at instruction 463, base `288`. -/
def loadPath463 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨463, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨464, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨465, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨466, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨467, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot read at instruction 547, base `800`. -/
def loadPath547 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨547, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨548, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨549, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨550, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨551, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot read at instruction 555, base `800`. -/
def loadPath555 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨555, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨556, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨557, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨558, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨559, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot read at instruction 595, base `800`. -/
def loadPath595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨595, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨596, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨597, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨598, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨599, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot read at instruction 603, base `800`. -/
def loadPath603 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨603, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨604, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨605, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨606, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨607, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot read at instruction 920, base `288`. -/
def loadPath920 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨920, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨921, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨922, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨923, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨924, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot write at instruction 472, base `288`. -/
def storePath472 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨472, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨473, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨474, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨475, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨476, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot write at instruction 517, base `800`. -/
def storePath517 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨517, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨518, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨519, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨520, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨521, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot write at instruction 913, base `800`. -/
def storePath913 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨913, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨914, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨915, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨916, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨917, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Inlined slot write at instruction 928, base `288`. -/
def storePath928 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨928, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨929, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨930, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨931, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨932, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

/-- The one inlined round-constant read: the `K` table is packed four
constants to a word, so the site adds a `SHR 224` to the address
computation. -/
def kAtPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨214, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨215, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨216, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨217, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨218, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨219, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨220, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Every inlined read has the same five-instruction shape, so one proof covers
all seven sites; only the base and the site's index vary.  The stepper's `ADD`
puts the base first, while `slotOffset` states the shift first, so each case
commutes the sum. -/
theorem run_slotLoad (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (index base : Nat) (slot : UInt256) (rest : List UInt256)
    (hmatch : (path = loadPath208 ∧ index = 208 ∧ base = 800) ∨
      (path = loadPath463 ∧ index = 463 ∧ base = 288) ∨
      (path = loadPath547 ∧ index = 547 ∧ base = 800) ∨
      (path = loadPath555 ∧ index = 555 ∧ base = 800) ∨
      (path = loadPath595 ∧ index = 595 ∧ base = 800) ∨
      (path = loadPath603 ∧ index = 603 ∧ base = 800) ∨
      (path = loadPath920 ∧ index = 920 ∧ base = 288))
    (hcap : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (slotEntry s index slot rest) =
        some (loadReturned s index base slot rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hd2 : rest.length + 1 + 1 < 1024 := by omega
  have hoff : UInt256.ofNat base + UInt256.shiftLeft slot (UInt256.ofNat 5) =
      UInt256.shiftLeft slot (UInt256.ofNat 5) + UInt256.ofNat base :=
    Challenge.EvmProof.Word.word_add_comm _ _
  rcases hmatch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    simp [loadPath208, loadPath463, loadPath547, loadPath555, loadPath595, loadPath603, loadPath920,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      slotEntry, loadReturned, slotOffset, hc1, hd2, hrun, hoff,
      State.activeWordsAfterUInt256]

/-- The same, for the four inlined writes. -/
theorem run_slotStore (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (index base : Nat) (slot value : UInt256) (rest : List UInt256)
    (hmatch : (path = storePath472 ∧ index = 472 ∧ base = 288) ∨
      (path = storePath517 ∧ index = 517 ∧ base = 800) ∨
      (path = storePath913 ∧ index = 913 ∧ base = 800) ∨
      (path = storePath928 ∧ index = 928 ∧ base = 288))
    (hcap : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (storeEntry s index slot value rest) =
        some (storeReturned s index base slot value rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hd2 : rest.length + 1 + 1 < 1024 := by omega
  have hd3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hoff : UInt256.ofNat base + UInt256.shiftLeft slot (UInt256.ofNat 5) =
      UInt256.shiftLeft slot (UInt256.ofNat 5) + UInt256.ofNat base :=
    Challenge.EvmProof.Word.word_add_comm _ _
  rcases hmatch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    simp [storePath472, storePath517, storePath913, storePath928,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      storeEntry, storeReturned, slotOffset, hd2, hd3, hrun, hoff,
      State.activeWordsAfterUInt256]

theorem run_kAt (s : State) (slot : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock kAtPath
      (slotEntry s 214 slot rest) = some (kAtReturned s slot rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hoff : UInt256.ofNat 32 + UInt256.shiftLeft slot (UInt256.ofNat 2) =
      UInt256.shiftLeft slot (UInt256.ofNat 2) + UInt256.ofNat 32 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp [kAtPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    slotEntry, kAtReturned, hc1, hc2, hrun, hoff,
    State.activeWordsAfterUInt256]

/-! ### `GasSteps` wrappers

`runLocatedBlock_sound` still needs the target-side frame facts, so these carry
`hcode`/`hfork`/`hnp` even though the run lemmas above do not. -/

def gasSteps_slotLoad (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (index base : Nat) (slot : UInt256) (rest : List UInt256)
    (hmatch : (path = loadPath208 ∧ index = 208 ∧ base = 800) ∨
      (path = loadPath463 ∧ index = 463 ∧ base = 288) ∨
      (path = loadPath547 ∧ index = 547 ∧ base = 800) ∨
      (path = loadPath555 ∧ index = 555 ∧ base = 800) ∨
      (path = loadPath595 ∧ index = 595 ∧ base = 800) ∨
      (path = loadPath603 ∧ index = 603 ∧ base = 800) ∨
      (path = loadPath920 ∧ index = 920 ∧ base = 288))
    (hcap : rest.length < 1021)
    (hcode : (slotEntry s index slot rest).executionEnv.code = referenceBytecode)
    (hfork : (slotEntry s index slot rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (slotEntry s index slot rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (slotEntry s index slot rest).executionEnv.precompileConfig
      (slotEntry s index slot rest).executionEnv.fork
      (slotEntry s index slot rest).executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (slotEntry s index slot rest)
      (loadReturned s index base slot rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact run_slotLoad path s index base slot rest hmatch hcap hrun
  · exact hhalt
  · exact hnp

def gasSteps_slotStore (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (index base : Nat) (slot value : UInt256) (rest : List UInt256)
    (hmatch : (path = storePath472 ∧ index = 472 ∧ base = 288) ∨
      (path = storePath517 ∧ index = 517 ∧ base = 800) ∨
      (path = storePath913 ∧ index = 913 ∧ base = 800) ∨
      (path = storePath928 ∧ index = 928 ∧ base = 288))
    (hcap : rest.length < 1021)
    (hcode : (storeEntry s index slot value rest).executionEnv.code =
      referenceBytecode)
    (hfork : (storeEntry s index slot value rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (storeEntry s index slot value rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (storeEntry s index slot value rest).executionEnv.precompileConfig
      (storeEntry s index slot value rest).executionEnv.fork
      (storeEntry s index slot value rest).executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (storeEntry s index slot value rest)
      (storeReturned s index base slot value rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact run_slotStore path s index base slot value rest hmatch hcap hrun
  · exact hhalt
  · exact hnp

def gasSteps_kAt (s : State) (slot : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1021)
    (hcode : (slotEntry s 214 slot rest).executionEnv.code = referenceBytecode)
    (hfork : (slotEntry s 214 slot rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (slotEntry s 214 slot rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (slotEntry s 214 slot rest).executionEnv.precompileConfig
      (slotEntry s 214 slot rest).executionEnv.fork
      (slotEntry s 214 slot rest).executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (slotEntry s 214 slot rest)
      (kAtReturned s slot rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka kAtPath
  · exact hcode
  · exact hfork
  · exact run_kAt s slot rest hcap hrun
  · exact hhalt
  · exact hnp

end Challenge.Sha256.Reference.Proofs.Bytecode.Accessors
