import Challenge.Sha256.Submissions.Sha256Fast.Proofs.SchedIter

set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace Loop.Body

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open YulEvmCompiler Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.EvmProof.Word Challenge.Sha256.Fast

private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
@[evmStep] def initialSchedulePath : List (Located Loop.art .Osaka) :=
  [⟨2, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨4, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨5, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨6, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨7, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨8, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨9, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 384), by rfl, by decide⟩,
   ⟨10, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨11, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 292), by rfl, by decide⟩,
   ⟨12, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨13, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨14, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨15, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨16, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨17, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨18, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨19, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 296), by rfl, by decide⟩,
   ⟨20, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨21, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨22, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨23, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨24, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨25, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨26, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨27, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 300), by rfl, by decide⟩,
   ⟨28, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨29, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨30, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨31, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨32, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨33, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨34, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨35, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 304), by rfl, by decide⟩,
   ⟨36, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨37, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨38, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨39, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨40, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨41, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨42, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨43, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 308), by rfl, by decide⟩,
   ⟨44, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨45, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨46, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨47, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨48, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨49, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨50, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨51, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 312), by rfl, by decide⟩,
   ⟨52, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨53, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨54, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨55, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨56, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨57, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 576), by rfl, by decide⟩,
   ⟨58, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨59, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 316), by rfl, by decide⟩,
   ⟨60, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨61, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨62, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨63, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨64, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨65, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 608), by rfl, by decide⟩,
   ⟨66, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨67, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨68, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨69, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨70, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨71, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨72, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨73, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 640), by rfl, by decide⟩,
   ⟨74, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨75, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 324), by rfl, by decide⟩,
   ⟨76, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨77, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨78, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨79, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨80, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨81, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 672), by rfl, by decide⟩,
   ⟨82, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨83, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 328), by rfl, by decide⟩,
   ⟨84, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨85, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨86, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨87, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨88, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨89, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 704), by rfl, by decide⟩,
   ⟨90, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨91, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 332), by rfl, by decide⟩,
   ⟨92, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨93, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨94, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨95, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨96, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨97, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 736), by rfl, by decide⟩,
   ⟨98, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨99, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 336), by rfl, by decide⟩,
   ⟨100, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨101, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨102, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨103, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨104, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨105, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 768), by rfl, by decide⟩,
   ⟨106, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨107, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 340), by rfl, by decide⟩,
   ⟨108, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨109, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨110, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨111, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨112, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨113, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨114, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨115, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 344), by rfl, by decide⟩,
   ⟨116, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨117, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨118, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨119, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨120, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨121, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 832), by rfl, by decide⟩,
   ⟨122, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨123, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 348), by rfl, by decide⟩,
   ⟨124, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨125, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨126, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨127, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨128, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨129, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 864), by rfl, by decide⟩,
   ⟨130, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨131, Instr.push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨132, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩]

/-- The subroutine's straight-line prefix reads the sixteen big-endian words
from the staged block and stores their doubled representations in W[0..15]. -/
theorem run_initialSchedule (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 4)
    (hstack : s.stack = returnDest :: rest) :
    runLocatedBlock initialSchedulePath s =
      some { s with
        pc := UInt256.ofNat 295
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (s.memory)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 288) (UInt256.ofNat 224))).toNat 32)
          384)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 292) (UInt256.ofNat 224))).toNat 32)
          416)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 296) (UInt256.ofNat 224))).toNat 32)
          448)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 300) (UInt256.ofNat 224))).toNat 32)
          480)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 304) (UInt256.ofNat 224))).toNat 32)
          512)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 308) (UInt256.ofNat 224))).toNat 32)
          544)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 312) (UInt256.ofNat 224))).toNat 32)
          576)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 316) (UInt256.ofNat 224))).toNat 32)
          608)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 320) (UInt256.ofNat 224))).toNat 32)
          640)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 324) (UInt256.ofNat 224))).toNat 32)
          672)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 328) (UInt256.ofNat 224))).toNat 32)
          704)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 332) (UInt256.ofNat 224))).toNat 32)
          736)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 336) (UInt256.ofNat 224))).toNat 32)
          768)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 340) (UInt256.ofNat 224))).toNat 32)
          800)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 344) (UInt256.ofNat 224))).toNat 32)
          832)
          (Data.Bytes.natToBytesPadded (dbl (UInt256.shiftRight (MachineState.readWord s.memory 348) (UInt256.ofNat 224))).toNat 32)
          864
        stack := UInt256.ofNat 0 :: returnDest :: rest } := by
  evm_block hcap
@[evmStep] def scheduleHeadPath : List (Located Loop.art .Osaka) :=
  [⟨132, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_scheduleHead (s : State) (u : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 294)
    (hstack : s.stack = u :: rest) :
    runLocatedBlock scheduleHeadPath s =
      some { s with pc := UInt256.ofNat 295 } := by
  evm_block hcap
@[evmStep] def prepareRoundsPath : List (Located Loop.art .Osaka) :=
  [⟨516, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.POP)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨517, Instr.push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨518, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨519, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨520, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨521, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨522, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨523, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨524, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨525, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨526, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨527, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨528, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨529, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨530, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨531, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨532, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨533, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨534, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩]

/-- Leave the schedule loop and load the current chaining state into the eight
fixed working stack slots. -/
theorem run_prepareRounds (s : State)
    (A B C D E F G H returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 884)
    (hstack : s.stack = UInt256.ofNat 1536 :: returnDest :: rest)
    (hA : MachineState.readWord s.memory 32 = A)
    (hB : MachineState.readWord s.memory 64 = B)
    (hC : MachineState.readWord s.memory 96 = C)
    (hD : MachineState.readWord s.memory 128 = D)
    (hE : MachineState.readWord s.memory 160 = E)
    (hF : MachineState.readWord s.memory 192 = F)
    (hG : MachineState.readWord s.memory 224 = G)
    (hH : MachineState.readWord s.memory 256 = H) :
    runLocatedBlock prepareRoundsPath s =
      some { s with
        pc := UInt256.ofNat 912
        activeWords := UInt256.ofNat 140
        stack := [A, B, C, D, E, F, G, H, UInt256.ofNat 0,
          returnDest] ++ rest } := by
  evm_block hcap

@[evmStep] def roundsHeadPath : List (Located Loop.art .Osaka) :=
  [⟨534, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)),
    by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_roundsHead (s : State)
    (stack : List UInt256) (hcap : stack.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 911)
    (hstack : s.stack = stack) :
    runLocatedBlock roundsHeadPath s =
      some { s with pc := UInt256.ofNat 912 } := by
  evm_block hcap

end Loop.Body
