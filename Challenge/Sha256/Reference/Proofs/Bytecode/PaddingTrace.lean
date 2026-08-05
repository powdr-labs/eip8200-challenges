import Challenge.Sha256.Reference.Proofs.Bytecode.Padding
import Challenge.Sha256.Reference.Proofs.Bytecode.Trace
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Meter
import YulEvmCompiler.BytesLemmas
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Direct execution of the reference padding code

The optimized artifact inlines `pad` into the program entry, so there is no call
into it and no function frame: initialization ends at instruction 48 and the
padded-length arithmetic begins there on an empty stack.  Gone with the call are
the return address and the zero output slot the old proof carried on the stack
through every state in this module, and with them `pushedReturn`,
`pushedOutput`, `pushedPad`, `padEntry`, `padBodyStart`, `gasSteps_enterPad` and
`gasSteps_padReadSize`.

Three blocks run here: the padded-length arithmetic (48..55), the
copy/sentinel/bit-length setup that jumps into the footer loop (56..79), and the
loop itself — condition at 145..150, body at 160..178, exit at 151..156.  The
backend inverted the loop's branch: the condition now jumps *to* the body when
`i < 8` rather than testing `iszero` and jumping to the exit, so the condition
and body are separate blocks instead of one fall-through path.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-! Initialization ends at instruction 48 on an empty stack.  `Main` states this
only through the `applyInitStore` fold, so the accessors the run proofs need are
reduced here. -/

@[simp] private theorem initializedState_pc (input : ByteArray) :
    (Main.initializedState input).pc = UInt256.ofNat 361 := by rfl
@[simp] private theorem initializedState_pcToNat (input : ByteArray) :
    (Main.initializedState input).pc.toNat = 361 := by rfl
@[simp] private theorem initializedState_stack (input : ByteArray) :
    (Main.initializedState input).stack = [] := by rfl
@[simp] private theorem initializedState_halt (input : ByteArray) :
    (Main.initializedState input).halt = .Running := by rfl
@[simp] private theorem initializedState_fork (input : ByteArray) :
    (Main.initializedState input).fork = .Osaka := by rfl
@[simp] private theorem initializedState_code (input : ByteArray) :
    (Main.initializedState input).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem initializedState_calldata (input : ByteArray) :
    (Main.initializedState input).executionEnv.calldata = input := by rfl

/-! Instruction PCs for the three blocks this module executes: the
padded-length arithmetic (48..55), the copy/sentinel/bit-length setup
(56..79), the footer loop's condition (145..150) and body (160..178), and
its exit (151..156). -/

@[simp] private theorem pc48 : Artifact.instructionPC 48 = 361 := by decide
@[simp] private theorem pc49 : Artifact.instructionPC 49 = 362 := by decide
@[simp] private theorem pc50 : Artifact.instructionPC 50 = 364 := by decide
@[simp] private theorem pc51 : Artifact.instructionPC 51 = 365 := by decide
@[simp] private theorem pc52 : Artifact.instructionPC 52 = 366 := by decide
@[simp] private theorem pc53 : Artifact.instructionPC 53 = 368 := by decide
@[simp] private theorem pc54 : Artifact.instructionPC 54 = 369 := by decide
@[simp] private theorem pc55 : Artifact.instructionPC 55 = 371 := by decide
@[simp] private theorem pc56 : Artifact.instructionPC 56 = 372 := by decide
@[simp] private theorem pc57 : Artifact.instructionPC 57 = 373 := by decide
@[simp] private theorem pc58 : Artifact.instructionPC 58 = 376 := by decide
@[simp] private theorem pc59 : Artifact.instructionPC 59 = 377 := by decide
@[simp] private theorem pc60 : Artifact.instructionPC 60 = 378 := by decide
@[simp] private theorem pc61 : Artifact.instructionPC 61 = 379 := by decide
@[simp] private theorem pc62 : Artifact.instructionPC 62 = 380 := by decide
@[simp] private theorem pc63 : Artifact.instructionPC 63 = 382 := by decide
@[simp] private theorem pc64 : Artifact.instructionPC 64 = 385 := by decide
@[simp] private theorem pc65 : Artifact.instructionPC 65 = 386 := by decide
@[simp] private theorem pc66 : Artifact.instructionPC 66 = 387 := by decide
@[simp] private theorem pc67 : Artifact.instructionPC 67 = 388 := by decide
@[simp] private theorem pc68 : Artifact.instructionPC 68 = 390 := by decide
@[simp] private theorem pc69 : Artifact.instructionPC 69 = 391 := by decide
@[simp] private theorem pc70 : Artifact.instructionPC 70 = 392 := by decide
@[simp] private theorem pc71 : Artifact.instructionPC 71 = 393 := by decide
@[simp] private theorem pc72 : Artifact.instructionPC 72 = 394 := by decide
@[simp] private theorem pc73 : Artifact.instructionPC 73 = 396 := by decide
@[simp] private theorem pc74 : Artifact.instructionPC 74 = 397 := by decide
@[simp] private theorem pc75 : Artifact.instructionPC 75 = 398 := by decide
@[simp] private theorem pc76 : Artifact.instructionPC 76 = 401 := by decide
@[simp] private theorem pc77 : Artifact.instructionPC 77 = 402 := by decide
@[simp] private theorem pc78 : Artifact.instructionPC 78 = 403 := by decide
@[simp] private theorem pc79 : Artifact.instructionPC 79 = 406 := by decide
@[simp] private theorem pc80 : Artifact.instructionPC 80 = 407 := by decide
@[simp] private theorem pc145 : Artifact.instructionPC 145 = 508 := by decide
@[simp] private theorem pc146 : Artifact.instructionPC 146 = 509 := by decide
@[simp] private theorem pc147 : Artifact.instructionPC 147 = 511 := by decide
@[simp] private theorem pc148 : Artifact.instructionPC 148 = 512 := by decide
@[simp] private theorem pc149 : Artifact.instructionPC 149 = 513 := by decide
@[simp] private theorem pc150 : Artifact.instructionPC 150 = 516 := by decide
@[simp] private theorem pc151 : Artifact.instructionPC 151 = 517 := by decide
@[simp] private theorem pc152 : Artifact.instructionPC 152 = 518 := by decide
@[simp] private theorem pc153 : Artifact.instructionPC 153 = 519 := by decide
@[simp] private theorem pc154 : Artifact.instructionPC 154 = 520 := by decide
@[simp] private theorem pc155 : Artifact.instructionPC 155 = 521 := by decide
@[simp] private theorem pc156 : Artifact.instructionPC 156 = 524 := by decide
@[simp] private theorem pc157 : Artifact.instructionPC 157 = 525 := by decide
@[simp] private theorem pc160 : Artifact.instructionPC 160 = 530 := by decide
@[simp] private theorem pc161 : Artifact.instructionPC 161 = 531 := by decide
@[simp] private theorem pc162 : Artifact.instructionPC 162 = 533 := by decide
@[simp] private theorem pc163 : Artifact.instructionPC 163 = 534 := by decide
@[simp] private theorem pc164 : Artifact.instructionPC 164 = 536 := by decide
@[simp] private theorem pc165 : Artifact.instructionPC 165 = 537 := by decide
@[simp] private theorem pc166 : Artifact.instructionPC 166 = 539 := by decide
@[simp] private theorem pc167 : Artifact.instructionPC 167 = 540 := by decide
@[simp] private theorem pc168 : Artifact.instructionPC 168 = 541 := by decide
@[simp] private theorem pc169 : Artifact.instructionPC 169 = 542 := by decide
@[simp] private theorem pc170 : Artifact.instructionPC 170 = 543 := by decide
@[simp] private theorem pc171 : Artifact.instructionPC 171 = 544 := by decide
@[simp] private theorem pc172 : Artifact.instructionPC 172 = 545 := by decide
@[simp] private theorem pc173 : Artifact.instructionPC 173 = 546 := by decide
@[simp] private theorem pc174 : Artifact.instructionPC 174 = 547 := by decide
@[simp] private theorem pc175 : Artifact.instructionPC 175 = 548 := by decide
@[simp] private theorem pc176 : Artifact.instructionPC 176 = 550 := by decide
@[simp] private theorem pc177 : Artifact.instructionPC 177 = 551 := by decide
@[simp] private theorem pc178 : Artifact.instructionPC 178 = 554 := by decide
@[simp] private theorem pc179 : Artifact.instructionPC 179 = 555 := by decide

@[simp] private theorem refPc48 :
    Artifact.referenceArtifact.instructionPC 48 = 361 := by decide
@[simp] private theorem refPc49 :
    Artifact.referenceArtifact.instructionPC 49 = 362 := by decide
@[simp] private theorem refPc50 :
    Artifact.referenceArtifact.instructionPC 50 = 364 := by decide
@[simp] private theorem refPc51 :
    Artifact.referenceArtifact.instructionPC 51 = 365 := by decide
@[simp] private theorem refPc52 :
    Artifact.referenceArtifact.instructionPC 52 = 366 := by decide
@[simp] private theorem refPc53 :
    Artifact.referenceArtifact.instructionPC 53 = 368 := by decide
@[simp] private theorem refPc54 :
    Artifact.referenceArtifact.instructionPC 54 = 369 := by decide
@[simp] private theorem refPc55 :
    Artifact.referenceArtifact.instructionPC 55 = 371 := by decide
@[simp] private theorem refPc56 :
    Artifact.referenceArtifact.instructionPC 56 = 372 := by decide
@[simp] private theorem refPc57 :
    Artifact.referenceArtifact.instructionPC 57 = 373 := by decide
@[simp] private theorem refPc58 :
    Artifact.referenceArtifact.instructionPC 58 = 376 := by decide
@[simp] private theorem refPc59 :
    Artifact.referenceArtifact.instructionPC 59 = 377 := by decide
@[simp] private theorem refPc60 :
    Artifact.referenceArtifact.instructionPC 60 = 378 := by decide
@[simp] private theorem refPc61 :
    Artifact.referenceArtifact.instructionPC 61 = 379 := by decide
@[simp] private theorem refPc62 :
    Artifact.referenceArtifact.instructionPC 62 = 380 := by decide
@[simp] private theorem refPc63 :
    Artifact.referenceArtifact.instructionPC 63 = 382 := by decide
@[simp] private theorem refPc64 :
    Artifact.referenceArtifact.instructionPC 64 = 385 := by decide
@[simp] private theorem refPc65 :
    Artifact.referenceArtifact.instructionPC 65 = 386 := by decide
@[simp] private theorem refPc66 :
    Artifact.referenceArtifact.instructionPC 66 = 387 := by decide
@[simp] private theorem refPc67 :
    Artifact.referenceArtifact.instructionPC 67 = 388 := by decide
@[simp] private theorem refPc68 :
    Artifact.referenceArtifact.instructionPC 68 = 390 := by decide
@[simp] private theorem refPc69 :
    Artifact.referenceArtifact.instructionPC 69 = 391 := by decide
@[simp] private theorem refPc70 :
    Artifact.referenceArtifact.instructionPC 70 = 392 := by decide
@[simp] private theorem refPc71 :
    Artifact.referenceArtifact.instructionPC 71 = 393 := by decide
@[simp] private theorem refPc72 :
    Artifact.referenceArtifact.instructionPC 72 = 394 := by decide
@[simp] private theorem refPc73 :
    Artifact.referenceArtifact.instructionPC 73 = 396 := by decide
@[simp] private theorem refPc74 :
    Artifact.referenceArtifact.instructionPC 74 = 397 := by decide
@[simp] private theorem refPc75 :
    Artifact.referenceArtifact.instructionPC 75 = 398 := by decide
@[simp] private theorem refPc76 :
    Artifact.referenceArtifact.instructionPC 76 = 401 := by decide
@[simp] private theorem refPc77 :
    Artifact.referenceArtifact.instructionPC 77 = 402 := by decide
@[simp] private theorem refPc78 :
    Artifact.referenceArtifact.instructionPC 78 = 403 := by decide
@[simp] private theorem refPc79 :
    Artifact.referenceArtifact.instructionPC 79 = 406 := by decide
@[simp] private theorem refPc80 :
    Artifact.referenceArtifact.instructionPC 80 = 407 := by decide
@[simp] private theorem refPc145 :
    Artifact.referenceArtifact.instructionPC 145 = 508 := by decide
@[simp] private theorem refPc146 :
    Artifact.referenceArtifact.instructionPC 146 = 509 := by decide
@[simp] private theorem refPc147 :
    Artifact.referenceArtifact.instructionPC 147 = 511 := by decide
@[simp] private theorem refPc148 :
    Artifact.referenceArtifact.instructionPC 148 = 512 := by decide
@[simp] private theorem refPc149 :
    Artifact.referenceArtifact.instructionPC 149 = 513 := by decide
@[simp] private theorem refPc150 :
    Artifact.referenceArtifact.instructionPC 150 = 516 := by decide
@[simp] private theorem refPc151 :
    Artifact.referenceArtifact.instructionPC 151 = 517 := by decide
@[simp] private theorem refPc152 :
    Artifact.referenceArtifact.instructionPC 152 = 518 := by decide
@[simp] private theorem refPc153 :
    Artifact.referenceArtifact.instructionPC 153 = 519 := by decide
@[simp] private theorem refPc154 :
    Artifact.referenceArtifact.instructionPC 154 = 520 := by decide
@[simp] private theorem refPc155 :
    Artifact.referenceArtifact.instructionPC 155 = 521 := by decide
@[simp] private theorem refPc156 :
    Artifact.referenceArtifact.instructionPC 156 = 524 := by decide
@[simp] private theorem refPc157 :
    Artifact.referenceArtifact.instructionPC 157 = 525 := by decide
@[simp] private theorem refPc160 :
    Artifact.referenceArtifact.instructionPC 160 = 530 := by decide
@[simp] private theorem refPc161 :
    Artifact.referenceArtifact.instructionPC 161 = 531 := by decide
@[simp] private theorem refPc162 :
    Artifact.referenceArtifact.instructionPC 162 = 533 := by decide
@[simp] private theorem refPc163 :
    Artifact.referenceArtifact.instructionPC 163 = 534 := by decide
@[simp] private theorem refPc164 :
    Artifact.referenceArtifact.instructionPC 164 = 536 := by decide
@[simp] private theorem refPc165 :
    Artifact.referenceArtifact.instructionPC 165 = 537 := by decide
@[simp] private theorem refPc166 :
    Artifact.referenceArtifact.instructionPC 166 = 539 := by decide
@[simp] private theorem refPc167 :
    Artifact.referenceArtifact.instructionPC 167 = 540 := by decide
@[simp] private theorem refPc168 :
    Artifact.referenceArtifact.instructionPC 168 = 541 := by decide
@[simp] private theorem refPc169 :
    Artifact.referenceArtifact.instructionPC 169 = 542 := by decide
@[simp] private theorem refPc170 :
    Artifact.referenceArtifact.instructionPC 170 = 543 := by decide
@[simp] private theorem refPc171 :
    Artifact.referenceArtifact.instructionPC 171 = 544 := by decide
@[simp] private theorem refPc172 :
    Artifact.referenceArtifact.instructionPC 172 = 545 := by decide
@[simp] private theorem refPc173 :
    Artifact.referenceArtifact.instructionPC 173 = 546 := by decide
@[simp] private theorem refPc174 :
    Artifact.referenceArtifact.instructionPC 174 = 547 := by decide
@[simp] private theorem refPc175 :
    Artifact.referenceArtifact.instructionPC 175 = 548 := by decide
@[simp] private theorem refPc176 :
    Artifact.referenceArtifact.instructionPC 176 = 550 := by decide
@[simp] private theorem refPc177 :
    Artifact.referenceArtifact.instructionPC 177 = 551 := by decide
@[simp] private theorem refPc178 :
    Artifact.referenceArtifact.instructionPC 178 = 554 := by decide
@[simp] private theorem refPc179 :
    Artifact.referenceArtifact.instructionPC 179 = 555 := by decide

/-! Word-arithmetic normalizers for each `pc` advance in those blocks. -/

@[simp] private theorem next48 : (UInt256.ofNat 361).succ = UInt256.ofNat 362 := by decide
@[simp] private theorem next49 : UInt256.ofNat 362 + UInt256.ofNat 2 = UInt256.ofNat 364 := by decide
@[simp] private theorem next50 : (UInt256.ofNat 364).succ = UInt256.ofNat 365 := by decide
@[simp] private theorem next51 : (UInt256.ofNat 365).succ = UInt256.ofNat 366 := by decide
@[simp] private theorem next52 : UInt256.ofNat 366 + UInt256.ofNat 2 = UInt256.ofNat 368 := by decide
@[simp] private theorem next53 : (UInt256.ofNat 368).succ = UInt256.ofNat 369 := by decide
@[simp] private theorem next54 : UInt256.ofNat 369 + UInt256.ofNat 2 = UInt256.ofNat 371 := by decide
@[simp] private theorem next55 : (UInt256.ofNat 371).succ = UInt256.ofNat 372 := by decide
@[simp] private theorem next56 : (UInt256.ofNat 372).succ = UInt256.ofNat 373 := by decide
@[simp] private theorem next57 : UInt256.ofNat 373 + UInt256.ofNat 3 = UInt256.ofNat 376 := by decide
@[simp] private theorem next58 : (UInt256.ofNat 376).succ = UInt256.ofNat 377 := by decide
@[simp] private theorem next59 : (UInt256.ofNat 377).succ = UInt256.ofNat 378 := by decide
@[simp] private theorem next60 : (UInt256.ofNat 378).succ = UInt256.ofNat 379 := by decide
@[simp] private theorem next61 : (UInt256.ofNat 379).succ = UInt256.ofNat 380 := by decide
@[simp] private theorem next62 : UInt256.ofNat 380 + UInt256.ofNat 2 = UInt256.ofNat 382 := by decide
@[simp] private theorem next63 : UInt256.ofNat 382 + UInt256.ofNat 3 = UInt256.ofNat 385 := by decide
@[simp] private theorem next64 : (UInt256.ofNat 385).succ = UInt256.ofNat 386 := by decide
@[simp] private theorem next65 : (UInt256.ofNat 386).succ = UInt256.ofNat 387 := by decide
@[simp] private theorem next66 : (UInt256.ofNat 387).succ = UInt256.ofNat 388 := by decide
@[simp] private theorem next67 : UInt256.ofNat 388 + UInt256.ofNat 2 = UInt256.ofNat 390 := by decide
@[simp] private theorem next68 : (UInt256.ofNat 390).succ = UInt256.ofNat 391 := by decide
@[simp] private theorem next69 : (UInt256.ofNat 391).succ = UInt256.ofNat 392 := by decide
@[simp] private theorem next70 : (UInt256.ofNat 392).succ = UInt256.ofNat 393 := by decide
@[simp] private theorem next71 : (UInt256.ofNat 393).succ = UInt256.ofNat 394 := by decide
@[simp] private theorem next72 : UInt256.ofNat 394 + UInt256.ofNat 2 = UInt256.ofNat 396 := by decide
@[simp] private theorem next73 : (UInt256.ofNat 396).succ = UInt256.ofNat 397 := by decide
@[simp] private theorem next74 : (UInt256.ofNat 397).succ = UInt256.ofNat 398 := by decide
@[simp] private theorem next75 : UInt256.ofNat 398 + UInt256.ofNat 3 = UInt256.ofNat 401 := by decide
@[simp] private theorem next76 : (UInt256.ofNat 401).succ = UInt256.ofNat 402 := by decide
@[simp] private theorem next77 : (UInt256.ofNat 402).succ = UInt256.ofNat 403 := by decide
@[simp] private theorem next78 : UInt256.ofNat 403 + UInt256.ofNat 3 = UInt256.ofNat 406 := by decide
@[simp] private theorem next79 : (UInt256.ofNat 406).succ = UInt256.ofNat 407 := by decide
@[simp] private theorem next145 : (UInt256.ofNat 508).succ = UInt256.ofNat 509 := by decide
@[simp] private theorem next146 : UInt256.ofNat 509 + UInt256.ofNat 2 = UInt256.ofNat 511 := by decide
@[simp] private theorem next147 : (UInt256.ofNat 511).succ = UInt256.ofNat 512 := by decide
@[simp] private theorem next148 : (UInt256.ofNat 512).succ = UInt256.ofNat 513 := by decide
@[simp] private theorem next149 : UInt256.ofNat 513 + UInt256.ofNat 3 = UInt256.ofNat 516 := by decide
@[simp] private theorem next150 : (UInt256.ofNat 516).succ = UInt256.ofNat 517 := by decide
@[simp] private theorem next151 : (UInt256.ofNat 517).succ = UInt256.ofNat 518 := by decide
@[simp] private theorem next152 : (UInt256.ofNat 518).succ = UInt256.ofNat 519 := by decide
@[simp] private theorem next153 : (UInt256.ofNat 519).succ = UInt256.ofNat 520 := by decide
@[simp] private theorem next154 : (UInt256.ofNat 520).succ = UInt256.ofNat 521 := by decide
@[simp] private theorem next155 : UInt256.ofNat 521 + UInt256.ofNat 3 = UInt256.ofNat 524 := by decide
@[simp] private theorem next156 : (UInt256.ofNat 524).succ = UInt256.ofNat 525 := by decide
@[simp] private theorem next160 : (UInt256.ofNat 530).succ = UInt256.ofNat 531 := by decide
@[simp] private theorem next161 : UInt256.ofNat 531 + UInt256.ofNat 2 = UInt256.ofNat 533 := by decide
@[simp] private theorem next162 : (UInt256.ofNat 533).succ = UInt256.ofNat 534 := by decide
@[simp] private theorem next163 : UInt256.ofNat 534 + UInt256.ofNat 2 = UInt256.ofNat 536 := by decide
@[simp] private theorem next164 : (UInt256.ofNat 536).succ = UInt256.ofNat 537 := by decide
@[simp] private theorem next165 : UInt256.ofNat 537 + UInt256.ofNat 2 = UInt256.ofNat 539 := by decide
@[simp] private theorem next166 : (UInt256.ofNat 539).succ = UInt256.ofNat 540 := by decide
@[simp] private theorem next167 : (UInt256.ofNat 540).succ = UInt256.ofNat 541 := by decide
@[simp] private theorem next168 : (UInt256.ofNat 541).succ = UInt256.ofNat 542 := by decide
@[simp] private theorem next169 : (UInt256.ofNat 542).succ = UInt256.ofNat 543 := by decide
@[simp] private theorem next170 : (UInt256.ofNat 543).succ = UInt256.ofNat 544 := by decide
@[simp] private theorem next171 : (UInt256.ofNat 544).succ = UInt256.ofNat 545 := by decide
@[simp] private theorem next172 : (UInt256.ofNat 545).succ = UInt256.ofNat 546 := by decide
@[simp] private theorem next173 : (UInt256.ofNat 546).succ = UInt256.ofNat 547 := by decide
@[simp] private theorem next174 : (UInt256.ofNat 547).succ = UInt256.ofNat 548 := by decide
@[simp] private theorem next175 : UInt256.ofNat 548 + UInt256.ofNat 2 = UInt256.ofNat 550 := by decide
@[simp] private theorem next176 : (UInt256.ofNat 550).succ = UInt256.ofNat 551 := by decide
@[simp] private theorem next177 : UInt256.ofNat 551 + UInt256.ofNat 3 = UInt256.ofNat 554 := by decide
@[simp] private theorem next178 : (UInt256.ofNat 554).succ = UInt256.ofNat 555 := by decide

/-! ### The padded-length arithmetic

`Main.initializedState` leaves the stack empty at instruction 48, so this block
runs on nothing and ends holding `[paddedWord, calldatasize]`.  The old layout
ended `[calldatasize, paddedWord, returnAddress]` and then dropped a slot with
`SWAP2; POP`; the new schedule keeps the padded word on top and never pushes the
frame at all. -/

def padSized (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := UInt256.ofNat (Artifact.instructionPC 49)
    stack := [UInt256.ofNat input.size] }

private def p49 (input : ByteArray) : State :=
  { padSized input with
    pc := UInt256.ofNat (Artifact.instructionPC 50)
    stack := [UInt256.ofNat 72, UInt256.ofNat input.size] }

private def p50 (input : ByteArray) : State :=
  { p49 input with
    pc := UInt256.ofNat (Artifact.instructionPC 51)
    stack := [UInt256.ofNat input.size, UInt256.ofNat 72,
      UInt256.ofNat input.size] }

private def p51 (input : ByteArray) : State :=
  { p50 input with
    pc := UInt256.ofNat (Artifact.instructionPC 52)
    stack := [UInt256.ofNat input.size + UInt256.ofNat 72,
      UInt256.ofNat input.size] }

private def p52 (input : ByteArray) : State :=
  { p51 input with
    pc := UInt256.ofNat (Artifact.instructionPC 53)
    stack := [UInt256.ofNat 6, UInt256.ofNat input.size + UInt256.ofNat 72,
      UInt256.ofNat input.size] }

private def p53 (input : ByteArray) : State :=
  { p52 input with
    pc := UInt256.ofNat (Artifact.instructionPC 54)
    stack := [UInt256.shiftRight
        (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6),
      UInt256.ofNat input.size] }

private def p54 (input : ByteArray) : State :=
  { p53 input with
    pc := UInt256.ofNat (Artifact.instructionPC 55)
    stack := [UInt256.ofNat 6,
      UInt256.shiftRight
        (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6),
      UInt256.ofNat input.size] }

/-- End of the padded-length block: `[paddedWord, calldatasize]`. -/
def padLengthReady (input : ByteArray) : State :=
  { p54 input with
    pc := UInt256.ofNat (Artifact.instructionPC 56)
    stack := [Padding.paddedWord input, UInt256.ofNat input.size] }

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  UInt256.ofNat Padding.messageOffset +
    (Padding.paddedWord input - UInt256.ofNat 8)

/-! ### Copy, sentinel, and footer-loop entry -/

def padCopied (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 62)
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 67)
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

/-- Entry to the fixed eight-iteration loop that stores the big-endian bit
length.  The calldata bytes and the `0x80` sentinel are already in memory, and
the dead `calldatasize` slot the old layout kept below the frame is gone. -/
def lengthLoopStart (input : ByteArray) : State :=
  { padSentinel input with
    pc := UInt256.ofNat (Artifact.instructionPC 145)
    stack := [⟨0⟩, lengthOffsetWord input, bitLengthWord input,
      Padding.paddedWord input] }

/-! ### The footer loop -/

def lengthByteWord (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight (bitLengthWord input)
      (UInt256.shiftLeft (UInt256.ofNat 7 - UInt256.ofNat i)
        (UInt256.ofNat 3)))
    (UInt256.ofNat 255)

def lengthLoopMemory (input : ByteArray) : Nat → ByteArray
  | 0 => (padSentinel input).memory
  | i + 1 => MachineState.writeBytes (lengthLoopMemory input i)
      (ByteArray.mk #[UInt8.ofNat ((lengthByteWord input i).toNat % 256)])
      (lengthOffsetWord input + UInt256.ofNat i).toNat

def lengthLoopActiveWords (input : ByteArray) : Nat → UInt256
  | 0 => (padSentinel input).activeWords
  | i + 1 => UInt256.ofNat (MachineState.activeWordsAfter
      (lengthLoopActiveWords input i).toNat
      (lengthOffsetWord input + UInt256.ofNat i).toNat 1)

def lengthLoopState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopStart input with
    pc := UInt256.ofNat (Artifact.instructionPC 145)
    stack := [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
      Padding.paddedWord input]
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

/-! ### Per-iteration states -/

def lengthBodyState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 160) }

def lengthByteState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 171)
    stack := [lengthByteWord input i, UInt256.ofNat i,
      lengthOffsetWord input, bitLengthWord input,
      Padding.paddedWord input] }

def lengthStoredState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 175)
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthIncrementedState (input : ByteArray) (i : Nat) : State :=
  { lengthStoredState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 177)
    stack := [UInt256.ofNat 1 + UInt256.ofNat i, lengthOffsetWord input,
      bitLengthWord input, Padding.paddedWord input] }

/-! ### Exit states -/

def lengthExitComparedState (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat (Artifact.instructionPC 151)
    stack := [UInt256.ofNat 8, lengthOffsetWord input, bitLengthWord input,
      Padding.paddedWord input] }

def lengthExitPoppedState (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat (Artifact.instructionPC 154)
    stack := [Padding.paddedWord input] }

/-- State the padding code leaves behind.  With `pad` inlined there is no
return: the exit block pushes the initial block counter and jumps to the driver
loop's condition at `0x197`, so the padded byte length is the result and the
counter is already on top of it. -/
def padReturned (input : ByteArray) : State :=
  { lengthLoopState input 8 with
    pc := UInt256.ofNat (Artifact.instructionPC 80)
    stack := [⟨0⟩, Padding.paddedWord input] }

/-- The straight-line arithmetic rounding `input.size + 72` up to the next
64-byte boundary.  Also the reusable executable seam for gas metering and
participant bytecode-equivalence proofs. -/
def computePaddedLengthPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨48, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨49, .push ⟨1, by decide⟩ (UInt256.ofNat 72), by rfl, by decide⟩,
   ⟨50, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨51, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨52, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨53, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨54, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨55, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Calldata copy, `0x80` sentinel, bit-length computation, and the jump into
the footer loop's condition. -/
def lengthSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨56, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨57, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset), by rfl, by decide⟩,
   ⟨58, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨59, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨60, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨61, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨62, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨63, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset), by rfl, by decide⟩,
   ⟨64, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨65, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨66, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨67, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨68, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨69, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨70, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨71, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨72, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨73, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨74, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨75, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset), by rfl, by decide⟩,
   ⟨76, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨77, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨78, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1fc), by rfl, by decide⟩,
   ⟨79, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Loop condition.  Jumps to the body at `0x212` when `i < 8`. -/
def lengthConditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨145, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨146, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨147, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨148, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨149, .push ⟨2, by decide⟩ (UInt256.ofNat 0x212), by rfl, by decide⟩,
   ⟨150, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Extract the `i`-th big-endian byte of the bit length. -/
def lengthBytePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨160, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨161, .push ⟨1, by decide⟩ (UInt256.ofNat 255), by rfl, by decide⟩,
   ⟨162, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨163, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨164, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨165, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨166, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨167, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨168, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨169, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨170, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Store that byte at `lengthOffset + i`. -/
def lengthStorePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨171, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨172, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨173, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨174, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Advance the counter. -/
def lengthIncrementPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨175, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨176, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Jump back to the condition. -/
def lengthBackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨177, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1fc), by rfl, by decide⟩,
   ⟨178, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- The exit: the condition falling through at `i = 8`, then the three pops,
the initial block counter, and the jump to the driver loop. -/
def lengthExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨145, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨146, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨147, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨148, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨149, .push ⟨2, by decide⟩ (UInt256.ofNat 0x212), by rfl, by decide⟩,
   ⟨150, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨151, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨152, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨153, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨154, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨155, .push ⟨2, by decide⟩ (UInt256.ofNat 0x197), by rfl, by decide⟩,
   ⟨156, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-! Jump-destination certificates for the three targets this module jumps to:
the loop condition `0x1fc`, its body `0x212`, and the driver loop `0x197` the
exit block falls into. -/

@[simp] private theorem zeroWordToNat : (⟨0⟩ : UInt256).toNat = 0 := by rfl

@[simp] private theorem valid508 :
    Decode.isValidJumpDest referenceBytecode 508 = true := by
  rw [← refPc145]
  exact Artifact.isValidJumpDest_index 145 (by rfl)

@[simp] private theorem valid530 :
    Decode.isValidJumpDest referenceBytecode 530 = true := by
  rw [← refPc160]
  exact Artifact.isValidJumpDest_index 160 (by rfl)

@[simp] private theorem valid407 :
    Decode.isValidJumpDest referenceBytecode 407 = true := by
  rw [← refPc80]
  exact Artifact.isValidJumpDest_index 80 (by rfl)

/-! ### State accessors -/

@[simp] private theorem padSized_halt (input : ByteArray) :
    (padSized input).halt = .Running := by rfl
@[simp] private theorem padSized_fork (input : ByteArray) :
    (padSized input).fork = .Osaka := by rfl
@[simp] private theorem padSized_code (input : ByteArray) :
    (padSized input).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem padSized_calldata (input : ByteArray) :
    (padSized input).executionEnv.calldata = input := by rfl

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl
@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl
@[simp] private theorem padLengthReady_code (input : ByteArray) :
    (padLengthReady input).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl
@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat 372 := by rfl
@[simp] private theorem padLengthReady_pcToNat (input : ByteArray) :
    (padLengthReady input).pc.toNat = 372 := by rfl
@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 508 := by rfl
@[simp] private theorem lengthLoopState_pcToNat (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc.toNat = 508 := by rfl
@[simp] private theorem lengthBodyState_pc (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).pc = UInt256.ofNat 530 := by rfl
@[simp] private theorem lengthBodyState_pcToNat (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).pc.toNat = 530 := by rfl
@[simp] private theorem lengthBodyState_stack (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).stack =
      [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
        Padding.paddedWord input] := by rfl
@[simp] private theorem lengthBodyState_halt (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).halt = .Running := by rfl
@[simp] private theorem lengthBodyState_fork (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).fork = .Osaka := by rfl
@[simp] private theorem lengthBodyState_code (input : ByteArray) (i : Nat) :
    (lengthBodyState input i).executionEnv.code = referenceBytecode := by rfl

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack =
      [Padding.paddedWord input, UInt256.ofNat input.size] := by rfl

@[simp] private theorem padCopied_code (input : ByteArray) :
    (padCopied input).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem padSentinel_code (input : ByteArray) :
    (padSentinel input).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem lengthLoopStart_code (input : ByteArray) :
    (lengthLoopStart input).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl
@[simp] private theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl
@[simp] private theorem lengthLoopStart_halt (input : ByteArray) :
    (lengthLoopStart input).halt = .Running := by rfl
@[simp] private theorem lengthLoopState_activeWords (input : ByteArray)
    (i : Nat) :
    (lengthLoopState input i).activeWords = lengthLoopActiveWords input i := by
  rfl
@[simp] private theorem lengthLoopState_memory (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).memory = lengthLoopMemory input i := by rfl
@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl
@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl
@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
        Padding.paddedWord input] := by rfl

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 407 := by rfl
@[simp] theorem padReturned_stack (input : ByteArray) :
    (padReturned input).stack = [⟨0⟩, Padding.paddedWord input] := by rfl
@[simp] theorem padReturned_halt (input : ByteArray) :
    (padReturned input).halt = .Running := by rfl
@[simp] theorem padReturned_code (input : ByteArray) :
    (padReturned input).executionEnv.code = referenceBytecode := by rfl
@[simp] theorem padReturned_calldata (input : ByteArray) :
    (padReturned input).executionEnv.calldata = input := by rfl
@[simp] theorem padReturned_noPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig
        (padReturned input).executionEnv.precompileConfig
        (padReturned input).executionEnv.fork
      (padReturned input).executionEnv.codeAddr = false := by
  exact deployAddress_not_precompile

/-! ### Runs -/

set_option maxHeartbeats 400000 in
private theorem run_computePaddedLength (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock computePaddedLengthPath
      (Main.initializedState input) = some (padLengthReady input) := by
  simp [computePaddedLengthPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padSized, p49, p50, p51, p52, p53, p54, padLengthReady,
    Padding.paddedWord]

def gasSteps_computePaddedLength (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Main.initializedState input)
      (padLengthReady input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka computePaddedLengthPath
  · rfl
  · rfl
  · exact run_computePaddedLength input
  · rfl
  · exact deployAddress_not_precompile

set_option maxHeartbeats 2000000 in
private theorem run_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthSetupPath
      (padLengthReady input) = some (lengthLoopState input 0) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hoff : Padding.messageOffset < 2 ^ 256 := by decide
  have hsum : Padding.messageOffset + input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  -- the new schedule computes the sentinel offset as `size + messageOffset`
  have hsum' : input.size + Padding.messageOffset < 2 ^ 256 := by omega
  have hadd : (UInt256.ofNat input.size +
      UInt256.ofNat Padding.messageOffset).toNat =
      Padding.messageOffset + input.size := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat hsum',
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum',
      Nat.add_comm]
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hoffWord : (UInt256.ofNat Padding.messageOffset).toNat =
      Padding.messageOffset := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp [lengthSetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthLoopState, lengthLoopMemory, lengthLoopActiveWords, lengthLoopStart,
    padSentinel, padCopied, lengthOffsetWord, bitLengthWord,
    State.activeWordsAfterUInt256, List.exchange, hsizeWord, hoffWord,
    hzero, hadd]

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input)
      (lengthLoopState input 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthSetupPath
  · rfl
  · exact padLengthReady_fork input
  · exact run_lengthSetup input hfit
  · rfl
  · exact deployAddress_not_precompile

set_option maxHeartbeats 2000000 in
private theorem run_lengthCondition (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthConditionPath
      (lengthLoopState input i) = some (lengthBodyState input i) := by
  have hi256 : i < 2 ^ 256 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 8) =
      (UInt256.ofNat 1) := by
    simp only [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : (8 : Nat) < 2 ^ 256)]
    simp [hi]
  simp [lengthConditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthBodyState, hlt, UInt256.isTrue]

@[simp] private theorem lengthByteState_pc (input : ByteArray) (i : Nat) :
    (lengthByteState input i).pc = UInt256.ofNat 544 := by rfl
@[simp] private theorem lengthByteState_pcToNat (input : ByteArray) (i : Nat) :
    (lengthByteState input i).pc.toNat = 544 := by rfl
@[simp] private theorem lengthByteState_halt (input : ByteArray) (i : Nat) :
    (lengthByteState input i).halt = .Running := by rfl
@[simp] private theorem lengthByteState_fork (input : ByteArray) (i : Nat) :
    (lengthByteState input i).fork = .Osaka := by rfl
@[simp] private theorem lengthByteState_code (input : ByteArray) (i : Nat) :
    (lengthByteState input i).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem lengthByteState_stack (input : ByteArray) (i : Nat) :
    (lengthByteState input i).stack =
      [lengthByteWord input i, UInt256.ofNat i, lengthOffsetWord input,
        bitLengthWord input, Padding.paddedWord input] := by rfl

@[simp] private theorem lengthStoredState_pc (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).pc = UInt256.ofNat 548 := by rfl
@[simp] private theorem lengthStoredState_pcToNat (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).pc.toNat = 548 := by rfl
@[simp] private theorem lengthStoredState_halt (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).halt = .Running := by rfl
@[simp] private theorem lengthStoredState_fork (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).fork = .Osaka := by rfl
@[simp] private theorem lengthStoredState_code (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).executionEnv.code = referenceBytecode := by rfl
@[simp] private theorem lengthStoredState_stack (input : ByteArray) (i : Nat) :
    (lengthStoredState input i).stack =
      [UInt256.ofNat i, lengthOffsetWord input, bitLengthWord input,
        Padding.paddedWord input] := by rfl

@[simp] private theorem lengthIncrementedState_pc (input : ByteArray) (i : Nat) :
    (lengthIncrementedState input i).pc = UInt256.ofNat 551 := by rfl
@[simp] private theorem lengthIncrementedState_pcToNat (input : ByteArray)
    (i : Nat) : (lengthIncrementedState input i).pc.toNat = 551 := by rfl
@[simp] private theorem lengthIncrementedState_halt (input : ByteArray)
    (i : Nat) : (lengthIncrementedState input i).halt = .Running := by rfl
@[simp] private theorem lengthIncrementedState_fork (input : ByteArray)
    (i : Nat) : (lengthIncrementedState input i).fork = .Osaka := by rfl
@[simp] private theorem lengthIncrementedState_code (input : ByteArray)
    (i : Nat) :
    (lengthIncrementedState input i).executionEnv.code = referenceBytecode := by
  rfl

set_option maxHeartbeats 2000000 in
private theorem run_lengthByte (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBytePath
      (lengthBodyState input i) = some (lengthByteState input i) := by
  simp [lengthBytePath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthBodyState, lengthByteState, lengthByteWord, List.exchange]

set_option maxHeartbeats 2000000 in
private theorem run_lengthStore (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthStorePath
      (lengthByteState input i) = some (lengthStoredState input i) := by
  -- the new schedule adds `i + lengthOffset`; `lengthLoopMemory` is stated in
  -- the other order so the spec-side lemmas below stay reusable
  have hcomm : UInt256.ofNat i + lengthOffsetWord input =
      lengthOffsetWord input + UInt256.ofNat i :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp [lengthStorePath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthByteState, lengthStoredState, lengthLoopMemory,
    lengthLoopActiveWords, State.activeWordsAfterUInt256, hcomm]

set_option maxHeartbeats 2000000 in
private theorem run_lengthIncrement (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthIncrementPath
      (lengthStoredState input i) = some (lengthIncrementedState input i) := by
  simp [lengthIncrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthIncrementedState]

set_option maxHeartbeats 2000000 in
private theorem run_lengthBack (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBackPath
      (lengthIncrementedState input i) = some (lengthLoopState input (i + 1)) := by
  have hsucc : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  simp [lengthBackPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthIncrementedState, lengthStoredState, lengthLoopState,
    lengthLoopStart, hsucc]

def gasSteps_lengthIteration (input : ByteArray) (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthLoopState input (i + 1)) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthConditionPath
    (lengthLoopState_code input i) (lengthLoopState_fork input i)
    (run_lengthCondition input i hi) (lengthLoopState_halt input i) (by rfl)
  have g₂ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthBytePath (by rfl) (by rfl)
    (run_lengthByte input i) (by rfl) (by rfl)
  have g₃ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthStorePath (by rfl) (by rfl)
    (run_lengthStore input i) (by rfl) (by rfl)
  have g₄ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthIncrementPath (by rfl) (by rfl)
    (run_lengthIncrement input i) (by rfl) (by rfl)
  have g₅ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthBackPath (by rfl) (by rfl)
    (run_lengthBack input i hi) (by rfl) (by rfl)
  exact g₁.trans (g₂.trans (g₃.trans (g₄.trans g₅)))

def gasSteps_lengthLoop (input : ByteArray) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 0)
      (lengthLoopState input 8) :=
  Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
    (I := lengthLoopState input)
    (fun i hi => gasSteps_lengthIteration input i hi)

set_option maxHeartbeats 2000000 in
private theorem run_lengthExit (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitPath
      (lengthLoopState input 8) = some (padReturned input) := by
  have hlt : UInt256.lt (UInt256.ofNat 8) (UInt256.ofNat 8) =
      (⟨0⟩ : UInt256) := by decide
  simp [lengthExitPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padReturned, hlt, UInt256.isTrue]

def gasSteps_lengthExit (input : ByteArray) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 8)
      (padReturned input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka lengthExitPath
  · exact lengthLoopState_code input 8
  · exact lengthLoopState_fork input 8
  · exact run_lengthExit input
  · exact lengthLoopState_halt input 8
  · rfl

/-! ### Spec-level facts

These are statements about the padding *specification* — the bit-length bytes,
the offset arithmetic, and the memory image the loop builds.  None of them
mention an instruction index, so the re-schedule leaves them untouched. -/

theorem bitLengthWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    bitLengthWord input = UInt256.ofNat (input.size * 8) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hresult : input.size * 2 ^ 3 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  simpa [bitLengthWord] using
    (Challenge.EvmProof.Word.shiftLeft_ofNat hsize (by decide : 3 < 256) hresult)

private theorem seven_sub_word (i : Nat) (hi : i < 8) :
    UInt256.ofNat 7 - UInt256.ofNat i = UInt256.ofNat (7 - i) := by
  have hi256 : i < 2 ^ 256 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
  have h7Word : (UInt256.ofNat 7).toNat = 7 := by decide
  have hsmall : 7 - i < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.sub_le 7 i) (by norm_num)
  have hsubWord : (UInt256.ofNat (7 - i)).toNat = 7 - i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  apply Challenge.EvmProof.Word.word_ext
  change ((UInt256.ofNat 7).val - (UInt256.ofNat i).val).val = _
  rw [Fin.val_sub]
  change (UInt256.size - (UInt256.ofNat i).toNat +
    (UInt256.ofNat 7).toNat) % UInt256.size =
      (UInt256.ofNat (7 - i)).toNat
  rw [hiWord, h7Word, hsubWord]
  have hrearrange : UInt256.size - i + 7 = UInt256.size + (7 - i) := by
    change 2 ^ 256 - i + 7 = 2 ^ 256 + (7 - i)
    omega
  rw [hrearrange, Nat.add_mod]
  rw [Nat.mod_self, Nat.zero_add]
  change ((7 - i) % 2 ^ 256) % 2 ^ 256 = 7 - i
  rw [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall]

theorem lengthByteWord_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    (lengthByteWord input i).toNat =
      input.size * 8 / 256 ^ (7 - i) % 256 := by
  have hvalue : input.size * 8 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  have hshift : (7 - i) * 8 < 256 := by omega
  have hshiftValue : 7 - i < 2 ^ 256 := by omega
  have hshiftResult : (7 - i) * 2 ^ 3 < 2 ^ 256 := by omega
  have hshiftWord : UInt256.shiftLeft (UInt256.ofNat (7 - i))
      (UInt256.ofNat 3) = UInt256.ofNat ((7 - i) * 8) := by
    simpa using Challenge.EvmProof.Word.shiftLeft_ofNat hshiftValue
      (by decide : 3 < 256) hshiftResult
  rw [lengthByteWord, bitLengthWord_eq input hfit, seven_sub_word i hi,
    hshiftWord, Challenge.EvmProof.Word.shiftRight_ofNat hvalue hshift]
  simp only [UInt256.land, UInt256.toNat]
  have hland : (↑(Fin.land
      (UInt256.ofNat ((input.size * 8) >>> ((7 - i) * 8))).val
      (UInt256.ofNat 255).val) : Nat) =
      (UInt256.ofNat ((input.size * 8) >>> ((7 - i) * 8))).val.val &&&
        (UInt256.ofNat 255).val.val := by
    exact Fin.and_val _ _
  rw [hland]
  change (UInt256.ofNat ((input.size * 8) >>> ((7 - i) * 8))).toNat &&&
      (UInt256.ofNat 255).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hvalue)]
  have h255 : (UInt256.ofNat 255).toNat = 255 := by decide
  rw [h255, show 255 = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ ((7 - i) * 8) = 256 ^ (7 - i) by
    rw [Nat.mul_comm, Nat.pow_mul]]

theorem lengthByte_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    UInt8.ofNat ((lengthByteWord input i).toNat % 256) =
      (Padding.lengthBytes input)[i]?.getD 0 := by
  change UInt8.ofNat ((lengthByteWord input i).toNat % 256) =
    (Data.Bytes.natToBytesPadded (input.size * 8) 8)[i]?.getD 0
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
    (input.size * 8) 8 i hi]
  rw [show 8 - 1 - i = 7 - i by omega]
  rw [lengthByteWord_toNat input hfit i hi]
  simp only [Nat.mod_mod]

theorem lengthOffsetWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    lengthOffsetWord input = UInt256.ofNat
      (Padding.messageOffset + Padding.paddedLength input.size - 8) := by
  have hfooter := Padding.input_and_footer_fit input.size
  have hpadded : Padding.paddedLength input.size < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := Padding.paddedLength input.size) (b := 8) (by omega) hpadded
  have hsum : Padding.messageOffset +
      (Padding.paddedLength input.size - 8) < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    have hoffset : Padding.messageOffset + Padding.paddedLength input.size <
        2 ^ 256 := by
      calc
        Padding.messageOffset + Padding.paddedLength input.size <
            Padding.messageOffset + (input.size + 73) :=
          Nat.add_lt_add_left hlt _
        _ < 2 ^ 256 := by
          have hinput73 : input.size + 73 < 2 ^ 65 := by
            unfold CalldataFits at hfit
            norm_num at hfit ⊢
            omega
          calc
            Padding.messageOffset + (input.size + 73) <
                Padding.messageOffset + 2 ^ 65 :=
              Nat.add_lt_add_left hinput73 _
            _ < 2 ^ 256 := by norm_num [Padding.messageOffset]
    exact Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.sub_le (Padding.paddedLength input.size) 8) _)
      hoffset
  rw [lengthOffsetWord, Padding.paddedWord_eq input hfit, hsub,
    Challenge.EvmProof.Word.ofNat_add_ofNat hsum]
  congr 1
  omega

theorem lengthOffset_add_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
    (lengthOffsetWord input + UInt256.ofNat i).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 + i := by
  let base := Padding.messageOffset + Padding.paddedLength input.size - 8
  have hbase : base + i < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    dsimp only [base]
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  rw [lengthOffsetWord_eq input hfit,
    Challenge.EvmProof.Word.ofNat_add_ofNat hbase,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbase]

def lengthWrittenBytes (input : ByteArray) : Nat → ByteArray
  | 0 => ByteArray.empty
  | i + 1 => lengthWrittenBytes input i ++ ByteArray.mk #[
      (Padding.lengthBytes input)[i]?.getD 0]

@[simp] theorem lengthWrittenBytes_size (input : ByteArray) (i : Nat) :
    (lengthWrittenBytes input i).size = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [lengthWrittenBytes, ByteArray.size_append, ih]
      rfl

theorem lengthLoopMemory_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
    lengthLoopMemory input i = MachineState.writeBytes
      (padSentinel input).memory (lengthWrittenBytes input i)
      (Padding.messageOffset + Padding.paddedLength input.size - 8) := by
  induction i with
  | zero => simp [lengthLoopMemory, lengthWrittenBytes, MachineState.writeBytes]
  | succ i ih =>
      have hii : i < 8 := by omega
      rw [lengthLoopMemory, lengthWrittenBytes, lengthByte_eq input hfit i hii,
        lengthOffset_add_toNat input hfit i (by omega), ih (by omega)]
      simpa only [lengthWrittenBytes_size] using
        Challenge.EvmProof.Memory.writeBytes_append_adjacent
          (padSentinel input).memory (lengthWrittenBytes input i)
          (ByteArray.mk #[(Padding.lengthBytes input)[i]?.getD 0])
          (Padding.messageOffset + Padding.paddedLength input.size - 8)

theorem lengthWrittenBytes_getD (input : ByteArray) (i j : Nat) (hj : j < i) :
    (lengthWrittenBytes input i)[j]?.getD 0 =
      (Padding.lengthBytes input)[j]?.getD 0 := by
  induction i with
  | zero => omega
  | succ i ih =>
      rw [lengthWrittenBytes,
        Challenge.EvmProof.Memory.getElem?_getD_append,
        lengthWrittenBytes_size]
      by_cases hji : j < i
      · rw [if_pos hji]
        exact ih hji
      · have hjiEq : j = i := by omega
        subst j
        rw [if_neg (by omega)]
        rw [Nat.sub_self]
        rfl

theorem lengthWrittenBytes_eight (input : ByteArray) :
    lengthWrittenBytes input 8 = Padding.lengthBytes input := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂]
    exact lengthWrittenBytes_getD input 8 i (by simpa using hi₁)

theorem lengthLoopMemory_eight (input : ByteArray) (hfit : CalldataFits input) :
    lengthLoopMemory input 8 =
      Padding.paddedMemory (padLengthReady input).memory input := by
  rw [lengthLoopMemory_eq input hfit 8 (by omega), lengthWrittenBytes_eight]
  have hsentinel : (padSentinel input).memory =
      Padding.sentinelMemory (padLengthReady input).memory input := by
    simp [padSentinel, padCopied, Padding.sentinelMemory,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  rw [hsentinel]
  rfl

/-- The complete padding run: initialization, the padded-length arithmetic, the
copy/sentinel/bit-length setup, the eight-iteration footer loop, and the exit
into the driver loop.  Two links of the old chain are gone with the call —
`gasSteps_enterPad` and `gasSteps_padReadSize`. -/
def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (padReturned input) :=
  (Main.gasSteps_initialize input).trans
    ((gasSteps_computePaddedLength input).trans
      ((gasSteps_lengthSetup input hfit).trans
        ((gasSteps_lengthLoop input).trans (gasSteps_lengthExit input))))

theorem padReturned_memory (input : ByteArray) (hfit : CalldataFits input) :
    (padReturned input).memory =
      Padding.paddedMemory (padLengthReady input).memory input :=
  lengthLoopMemory_eight input hfit

/-- The instructions one loop iteration executes, in order.  The backend split
them across two blocks — the condition jumps to the body rather than falling
through — so this is a concatenation of the five sub-paths, not one straight
run.  The old layout's single `lengthIterationPath` ended with a trailing
`JUMPDEST` for the same reason in reverse. -/
def lengthIterationPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  lengthConditionPath ++ lengthBytePath ++ lengthStorePath ++
    lengthIncrementPath ++ lengthBackPath

/-- Static cost of the padded-length block: 23 gas.  The old block cost 26 — it
began with a `PUSH1` where this one begins with `CALLDATASIZE` (2 rather than 3)
and ended with the `SWAP2; POP` frame cleanup (5) the new schedule does not
need. -/
@[simp] theorem gasSteps_computePaddedLength_cost (input : ByteArray) :
    (gasSteps_computePaddedLength input).cost = 23 := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
    computePaddedLengthPath (Main.initializedState input) = 23
  have hstatic : ∀ located, located ∈ computePaddedLengthPath → ∀ q,
      q.fork = .Osaka →
        Challenge.EvmProof.Meter.instrCostWithoutMemory located.instruction q =
          Challenge.EvmProof.Meter.instrStaticCost .Osaka
            located.instruction := by
    intro located hlocated q _
    simp only [computePaddedLengthPath, List.mem_cons, List.not_mem_nil,
      or_false] at hlocated
    rcases hlocated with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]
  have hcost := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    computePaddedLengthPath (run_computePaddedLength input) (by rfl) hstatic
  have hwords : (padLengthReady input).activeWords =
      (Main.initializedState input).activeWords := by rfl
  rw [hwords] at hcost
  norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    computePaddedLengthPath, Challenge.EvmProof.Meter.instrStaticCost,
    Gas.baseCost] at hcost ⊢
  omega

end Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace
