import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverBlocks

set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.OutputBlock

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open YulEvmCompiler Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.EvmProof.Word Challenge.Sha256.Fast
open DriverBlocks

private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
@[evmStep] def outputPath : List (Located Loop.art .Osaka) :=
  [⟨1432, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1433, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨1434, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1435, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨1436, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1437, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1438, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1439, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨1440, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1441, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.OR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1442, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨1443, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1444, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨1445, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1446, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.OR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1447, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨1448, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1449, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨1450, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1451, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.OR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1452, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨1453, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1454, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨1455, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1456, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.OR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1457, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨1458, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1459, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1460, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1461, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.OR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1462, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨1463, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1464, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨1465, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1466, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.OR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1467, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨1468, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1469, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.OR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1470, Instr.push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨1471, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1472, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨1473, Instr.push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨1474, Instr.op (Operation.System (Operation.SystemOps.RETURN)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_output (s : State) (off endWord rem n : UInt256)
    (H0 H1 H2 H3 H4 H5 H6 H7 : UInt32)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2562)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hh0 : MachineState.readWord s.memory 32 = ofUInt32 H0)
    (hh1 : MachineState.readWord s.memory 64 = ofUInt32 H1)
    (hh2 : MachineState.readWord s.memory 96 = ofUInt32 H2)
    (hh3 : MachineState.readWord s.memory 128 = ofUInt32 H3)
    (hh4 : MachineState.readWord s.memory 160 = ofUInt32 H4)
    (hh5 : MachineState.readWord s.memory 192 = ofUInt32 H5)
    (hh6 : MachineState.readWord s.memory 224 = ofUInt32 H6)
    (hh7 : MachineState.readWord s.memory 256 = ofUInt32 H7) :
    runLocatedBlock outputPath s =
      some { s with
        pc := UInt256.ofNat 2621
        halt := .Returned
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (outputBytes H0 H1 H2 H3 H4 H5 H6 H7) 0
        hReturn := outputBytes H0 H1 H2 H3 H4 H5 H6 H7
        stack := [off, endWord, rem, n] ++ rest } := by
  evm_block hcap
  constructor
  · rfl
  · change MachineState.readPadded
        (MachineState.writeBytes s.memory
          (outputBytes H0 H1 H2 H3 H4 H5 H6 H7) 0) 0 32 =
        outputBytes H0 H1 H2 H3 H4 H5 H6 H7
    have hsize : (outputBytes H0 H1 H2 H3 H4 H5 H6 H7).size = 32 := by
      unfold outputBytes
      exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
    rw [← hsize]
    exact Challenge.EvmProof.Memory.readPadded_writeBytes_same s.memory
      (outputBytes H0 H1 H2 H3 H4 H5 H6 H7) 0

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.OutputBlock
