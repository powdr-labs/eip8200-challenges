import Challenge.Sha256.Submissions.Sha256Fast.Proofs.Body
import YulEvmCompiler.BytesLemmas

set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverBlocks

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open YulEvmCompiler Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.EvmProof.Word Challenge.Sha256.Fast

private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩

def hashMemory (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1779033703).toNat 32)
          32)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3144134277).toNat 32)
          64)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1013904242).toNat 32)
          96)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2773480762).toNat 32)
          128)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1359893119).toNat 32)
          160)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2600822924).toNat 32)
          192)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 528734635).toNat 32)
          224)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1541459225).toNat 32)
          256

def constantMemory0 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1116352408).toNat 32)
          2432)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1899447441).toNat 32)
          2464)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3049323471).toNat 32)
          2496)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3921009573).toNat 32)
          2528)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 961987163).toNat 32)
          2560)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1508970993).toNat 32)
          2592)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2453635748).toNat 32)
          2624)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2870763221).toNat 32)
          2656

def constantMemory1 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3624381080).toNat 32)
          2688)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 310598401).toNat 32)
          2720)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 607225278).toNat 32)
          2752)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1426881987).toNat 32)
          2784)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1925078388).toNat 32)
          2816)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2162078206).toNat 32)
          2848)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2614888103).toNat 32)
          2880)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3248222580).toNat 32)
          2912

def constantMemory2 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3835390401).toNat 32)
          2944)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 4022224774).toNat 32)
          2976)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 264347078).toNat 32)
          3008)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 604807628).toNat 32)
          3040)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 770255983).toNat 32)
          3072)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1249150122).toNat 32)
          3104)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1555081692).toNat 32)
          3136)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1996064986).toNat 32)
          3168

def constantMemory3 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2554220882).toNat 32)
          3200)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2821834349).toNat 32)
          3232)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2952996808).toNat 32)
          3264)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3210313671).toNat 32)
          3296)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3336571891).toNat 32)
          3328)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3584528711).toNat 32)
          3360)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 113926993).toNat 32)
          3392)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 338241895).toNat 32)
          3424

def constantMemory4 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 666307205).toNat 32)
          3456)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 773529912).toNat 32)
          3488)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1294757372).toNat 32)
          3520)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1396182291).toNat 32)
          3552)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1695183700).toNat 32)
          3584)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1986661051).toNat 32)
          3616)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2177026350).toNat 32)
          3648)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2456956037).toNat 32)
          3680

def constantMemory5 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2730485921).toNat 32)
          3712)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2820302411).toNat 32)
          3744)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3259730800).toNat 32)
          3776)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3345764771).toNat 32)
          3808)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3516065817).toNat 32)
          3840)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3600352804).toNat 32)
          3872)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 4094571909).toNat 32)
          3904)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 275423344).toNat 32)
          3936

def constantMemory6 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 430227734).toNat 32)
          3968)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 506948616).toNat 32)
          4000)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 659060556).toNat 32)
          4032)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 883997877).toNat 32)
          4064)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 958139571).toNat 32)
          4096)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1322822218).toNat 32)
          4128)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1537002063).toNat 32)
          4160)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1747873779).toNat 32)
          4192

def constantMemory7 (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 1955562222).toNat 32)
          4224)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2024104815).toNat 32)
          4256)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2227730452).toNat 32)
          4288)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2361852424).toNat 32)
          4320)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2428436474).toNat 32)
          4352)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 2756734187).toNat 32)
          4384)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3204031479).toNat 32)
          4416)
          (Data.Bytes.natToBytesPadded (UInt256.ofNat 3329325298).toNat 32)
          4448

def initializedMemory (memory : ByteArray) : ByteArray :=
  constantMemory7 (constantMemory6 (constantMemory5 (constantMemory4 (constantMemory3 (constantMemory2 (constantMemory1 (constantMemory0 (hashMemory memory))))))))

def foldedMemory (memory : ByteArray)
    (A B C D E F G H H0 H1 H2 H3 H4 H5 H6 H7 : UInt32) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (memory)
          (Data.Bytes.natToBytesPadded (ofUInt32 (A + H0)).toNat 32)
          32)
          (Data.Bytes.natToBytesPadded (ofUInt32 (B + H1)).toNat 32)
          64)
          (Data.Bytes.natToBytesPadded (ofUInt32 (C + H2)).toNat 32)
          96)
          (Data.Bytes.natToBytesPadded (ofUInt32 (D + H3)).toNat 32)
          128)
          (Data.Bytes.natToBytesPadded (ofUInt32 (E + H4)).toNat 32)
          160)
          (Data.Bytes.natToBytesPadded (ofUInt32 (F + H5)).toNat 32)
          192)
          (Data.Bytes.natToBytesPadded (ofUInt32 (G + H6)).toNat 32)
          224)
          (Data.Bytes.natToBytesPadded (ofUInt32 (H + H7)).toNat 32)
          256
@[evmStep] def feedForward0Path : List (Located Loop.art .Osaka) :=
  [⟨1089, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨1090, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1091, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1092, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1093, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1094, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨1095, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward0 (s : State) (A H0 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1696)
    (hstack : s.stack = [ofUInt32 A, ofUInt32 B, ofUInt32 C, ofUInt32 D, ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 32 = ofUInt32 H0) :
    runLocatedBlock feedForward0Path s =
      some { s with
        pc := UInt256.ofNat 1709
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (A + H0)).toNat 32)
          32
        stack := [ofUInt32 B, ofUInt32 C, ofUInt32 D, ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest } := by
  evm_block hcap
@[evmStep] def feedForward1Path : List (Located Loop.art .Osaka) :=
  [⟨1096, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1097, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1098, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1099, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1100, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1101, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1102, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward1 (s : State) (B H1 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1709)
    (hstack : s.stack = [ofUInt32 B, ofUInt32 C, ofUInt32 D, ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 64 = ofUInt32 H1) :
    runLocatedBlock feedForward1Path s =
      some { s with
        pc := UInt256.ofNat 1722
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (B + H1)).toNat 32)
          64
        stack := [ofUInt32 C, ofUInt32 D, ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest } := by
  evm_block hcap
@[evmStep] def feedForward2Path : List (Located Loop.art .Osaka) :=
  [⟨1103, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨1104, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1105, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1106, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1107, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1108, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨1109, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward2 (s : State) (C H2 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1722)
    (hstack : s.stack = [ofUInt32 C, ofUInt32 D, ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 96 = ofUInt32 H2) :
    runLocatedBlock feedForward2Path s =
      some { s with
        pc := UInt256.ofNat 1735
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (C + H2)).toNat 32)
          96
        stack := [ofUInt32 D, ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest } := by
  evm_block hcap
@[evmStep] def feedForward3Path : List (Located Loop.art .Osaka) :=
  [⟨1110, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨1111, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1112, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1113, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1114, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1115, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨1116, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward3 (s : State) (D H3 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1735)
    (hstack : s.stack = [ofUInt32 D, ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 128 = ofUInt32 H3) :
    runLocatedBlock feedForward3Path s =
      some { s with
        pc := UInt256.ofNat 1748
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (D + H3)).toNat 32)
          128
        stack := [ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest } := by
  evm_block hcap
@[evmStep] def feedForward4Path : List (Located Loop.art .Osaka) :=
  [⟨1117, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨1118, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1119, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1120, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1121, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1122, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨1123, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward4 (s : State) (E H4 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1748)
    (hstack : s.stack = [ofUInt32 E, ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 160 = ofUInt32 H4) :
    runLocatedBlock feedForward4Path s =
      some { s with
        pc := UInt256.ofNat 1761
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (E + H4)).toNat 32)
          160
        stack := [ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest } := by
  evm_block hcap
@[evmStep] def feedForward5Path : List (Located Loop.art .Osaka) :=
  [⟨1124, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨1125, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1126, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1127, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1128, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1129, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨1130, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward5 (s : State) (F H5 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1761)
    (hstack : s.stack = [ofUInt32 F, ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 192 = ofUInt32 H5) :
    runLocatedBlock feedForward5Path s =
      some { s with
        pc := UInt256.ofNat 1774
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (F + H5)).toNat 32)
          192
        stack := [ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest } := by
  evm_block hcap
@[evmStep] def feedForward6Path : List (Located Loop.art .Osaka) :=
  [⟨1131, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨1132, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1133, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1134, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1135, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1136, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨1137, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward6 (s : State) (G H6 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1774)
    (hstack : s.stack = [ofUInt32 G, ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 224 = ofUInt32 H6) :
    runLocatedBlock feedForward6Path s =
      some { s with
        pc := UInt256.ofNat 1787
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (G + H6)).toNat 32)
          224
        stack := [ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest } := by
  evm_block hcap
@[evmStep] def feedForward7Path : List (Located Loop.art .Osaka) :=
  [⟨1138, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨1139, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1140, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1141, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨1142, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1143, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨1144, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1145, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.POP)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1146, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMP)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_feedForward7 (s : State) (H H7 : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 999) (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hret : Decode.isValidJumpDest Loop.bytes returnDest.toNat = true)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1787)
    (hstack : s.stack = [ofUInt32 H, UInt256.ofNat 2048, returnDest] ++ rest)
    (hh : MachineState.readWord s.memory 256 = ofUInt32 H7) :
    runLocatedBlock feedForward7Path s =
      some { s with
        pc := returnDest
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 (H + H7)).toNat 32)
          256
        stack := rest } := by
  have hcap' : rest.length < 1000 := by omega
  have hret' : Decode.isValidJumpDest (YulEvmCompiler.assemble Loop.instrs) returnDest.toNat = true := by
    simpa [Loop.bytes] using hret
  evm_block hcap' <;> simp only [hret']
@[evmStep] def initializeEntryPath : List (Located Loop.art .Osaka) :=
  [⟨0, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1804), by rfl, by decide⟩,
   ⟨1, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMP)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeEntry (s : State)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hmain : Decode.isValidJumpDest Loop.bytes 1804 = true)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 0)
    (hstack : s.stack = []) :
    runLocatedBlock initializeEntryPath s =
      some { s with
        pc := UInt256.ofNat 1804 } := by
  have hmain' : Decode.isValidJumpDest
      (YulEvmCompiler.assemble Loop.instrs) 1804 = true := by
    simpa [Loop.bytes] using hmain
  evm_block <;> simp only [hmain']
@[evmStep] def initializeHashPath : List (Located Loop.art .Osaka) :=
  [⟨1147, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1148, Instr.op (Operation.Env (Operation.EnvOps.CALLDATASIZE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1149, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1779033703), by rfl, by decide⟩,
   ⟨1150, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨1151, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1152, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3144134277), by rfl, by decide⟩,
   ⟨1153, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1154, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1155, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1013904242), by rfl, by decide⟩,
   ⟨1156, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨1157, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1158, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2773480762), by rfl, by decide⟩,
   ⟨1159, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨1160, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1161, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1359893119), by rfl, by decide⟩,
   ⟨1162, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨1163, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1164, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2600822924), by rfl, by decide⟩,
   ⟨1165, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨1166, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1167, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 528734635), by rfl, by decide⟩,
   ⟨1168, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨1169, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1170, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1541459225), by rfl, by decide⟩,
   ⟨1171, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨1172, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeHash (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1804)
    (haw : s.activeWords = UInt256.ofNat 0) (hstack : s.stack = [])
    (hn : UInt256.ofNat s.executionEnv.calldata.size = n) :
    runLocatedBlock initializeHashPath s =
      some { s with
        pc := UInt256.ofNat 1871
        activeWords := UInt256.ofNat 9
        memory := hashMemory s.memory
        stack := [n] } := by
  evm_block <;> simp [hashMemory, word_toNat_ofNat]
@[evmStep] def initializeConstants0Path : List (Located Loop.art .Osaka) :=
  [⟨1173, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1116352408), by rfl, by decide⟩,
   ⟨1174, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2432), by rfl, by decide⟩,
   ⟨1175, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1176, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1899447441), by rfl, by decide⟩,
   ⟨1177, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2464), by rfl, by decide⟩,
   ⟨1178, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1179, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3049323471), by rfl, by decide⟩,
   ⟨1180, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2496), by rfl, by decide⟩,
   ⟨1181, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1182, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3921009573), by rfl, by decide⟩,
   ⟨1183, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2528), by rfl, by decide⟩,
   ⟨1184, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1185, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 961987163), by rfl, by decide⟩,
   ⟨1186, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2560), by rfl, by decide⟩,
   ⟨1187, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1188, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1508970993), by rfl, by decide⟩,
   ⟨1189, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2592), by rfl, by decide⟩,
   ⟨1190, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1191, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2453635748), by rfl, by decide⟩,
   ⟨1192, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2624), by rfl, by decide⟩,
   ⟨1193, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1194, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2870763221), by rfl, by decide⟩,
   ⟨1195, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2656), by rfl, by decide⟩,
   ⟨1196, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants0 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1871)
    (haw : s.activeWords = UInt256.ofNat 9)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants0Path s =
      some { s with
        pc := UInt256.ofNat 1943
        activeWords := UInt256.ofNat 84
        memory := constantMemory0 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory0, word_toNat_ofNat]
@[evmStep] def initializeConstants1Path : List (Located Loop.art .Osaka) :=
  [⟨1197, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3624381080), by rfl, by decide⟩,
   ⟨1198, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2688), by rfl, by decide⟩,
   ⟨1199, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1200, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 310598401), by rfl, by decide⟩,
   ⟨1201, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2720), by rfl, by decide⟩,
   ⟨1202, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1203, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 607225278), by rfl, by decide⟩,
   ⟨1204, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2752), by rfl, by decide⟩,
   ⟨1205, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1206, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1426881987), by rfl, by decide⟩,
   ⟨1207, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2784), by rfl, by decide⟩,
   ⟨1208, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1209, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1925078388), by rfl, by decide⟩,
   ⟨1210, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2816), by rfl, by decide⟩,
   ⟨1211, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1212, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2162078206), by rfl, by decide⟩,
   ⟨1213, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2848), by rfl, by decide⟩,
   ⟨1214, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1215, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2614888103), by rfl, by decide⟩,
   ⟨1216, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2880), by rfl, by decide⟩,
   ⟨1217, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1218, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3248222580), by rfl, by decide⟩,
   ⟨1219, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2912), by rfl, by decide⟩,
   ⟨1220, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants1 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1943)
    (haw : s.activeWords = UInt256.ofNat 84)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants1Path s =
      some { s with
        pc := UInt256.ofNat 2015
        activeWords := UInt256.ofNat 92
        memory := constantMemory1 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory1, word_toNat_ofNat]
@[evmStep] def initializeConstants2Path : List (Located Loop.art .Osaka) :=
  [⟨1221, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3835390401), by rfl, by decide⟩,
   ⟨1222, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2944), by rfl, by decide⟩,
   ⟨1223, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1224, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4022224774), by rfl, by decide⟩,
   ⟨1225, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2976), by rfl, by decide⟩,
   ⟨1226, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1227, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 264347078), by rfl, by decide⟩,
   ⟨1228, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3008), by rfl, by decide⟩,
   ⟨1229, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1230, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 604807628), by rfl, by decide⟩,
   ⟨1231, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3040), by rfl, by decide⟩,
   ⟨1232, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1233, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 770255983), by rfl, by decide⟩,
   ⟨1234, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3072), by rfl, by decide⟩,
   ⟨1235, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1236, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1249150122), by rfl, by decide⟩,
   ⟨1237, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3104), by rfl, by decide⟩,
   ⟨1238, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1239, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1555081692), by rfl, by decide⟩,
   ⟨1240, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3136), by rfl, by decide⟩,
   ⟨1241, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1242, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1996064986), by rfl, by decide⟩,
   ⟨1243, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3168), by rfl, by decide⟩,
   ⟨1244, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants2 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2015)
    (haw : s.activeWords = UInt256.ofNat 92)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants2Path s =
      some { s with
        pc := UInt256.ofNat 2087
        activeWords := UInt256.ofNat 100
        memory := constantMemory2 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory2, word_toNat_ofNat]
@[evmStep] def initializeConstants3Path : List (Located Loop.art .Osaka) :=
  [⟨1245, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2554220882), by rfl, by decide⟩,
   ⟨1246, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3200), by rfl, by decide⟩,
   ⟨1247, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1248, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2821834349), by rfl, by decide⟩,
   ⟨1249, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3232), by rfl, by decide⟩,
   ⟨1250, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1251, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2952996808), by rfl, by decide⟩,
   ⟨1252, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3264), by rfl, by decide⟩,
   ⟨1253, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1254, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3210313671), by rfl, by decide⟩,
   ⟨1255, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3296), by rfl, by decide⟩,
   ⟨1256, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1257, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3336571891), by rfl, by decide⟩,
   ⟨1258, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3328), by rfl, by decide⟩,
   ⟨1259, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1260, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3584528711), by rfl, by decide⟩,
   ⟨1261, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3360), by rfl, by decide⟩,
   ⟨1262, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1263, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 113926993), by rfl, by decide⟩,
   ⟨1264, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3392), by rfl, by decide⟩,
   ⟨1265, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1266, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 338241895), by rfl, by decide⟩,
   ⟨1267, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3424), by rfl, by decide⟩,
   ⟨1268, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants3 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2087)
    (haw : s.activeWords = UInt256.ofNat 100)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants3Path s =
      some { s with
        pc := UInt256.ofNat 2159
        activeWords := UInt256.ofNat 108
        memory := constantMemory3 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory3, word_toNat_ofNat]
@[evmStep] def initializeConstants4Path : List (Located Loop.art .Osaka) :=
  [⟨1269, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 666307205), by rfl, by decide⟩,
   ⟨1270, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3456), by rfl, by decide⟩,
   ⟨1271, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1272, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 773529912), by rfl, by decide⟩,
   ⟨1273, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3488), by rfl, by decide⟩,
   ⟨1274, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1275, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1294757372), by rfl, by decide⟩,
   ⟨1276, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3520), by rfl, by decide⟩,
   ⟨1277, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1278, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1396182291), by rfl, by decide⟩,
   ⟨1279, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3552), by rfl, by decide⟩,
   ⟨1280, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1281, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1695183700), by rfl, by decide⟩,
   ⟨1282, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3584), by rfl, by decide⟩,
   ⟨1283, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1284, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1986661051), by rfl, by decide⟩,
   ⟨1285, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3616), by rfl, by decide⟩,
   ⟨1286, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1287, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2177026350), by rfl, by decide⟩,
   ⟨1288, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3648), by rfl, by decide⟩,
   ⟨1289, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1290, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2456956037), by rfl, by decide⟩,
   ⟨1291, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3680), by rfl, by decide⟩,
   ⟨1292, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants4 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2159)
    (haw : s.activeWords = UInt256.ofNat 108)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants4Path s =
      some { s with
        pc := UInt256.ofNat 2231
        activeWords := UInt256.ofNat 116
        memory := constantMemory4 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory4, word_toNat_ofNat]
@[evmStep] def initializeConstants5Path : List (Located Loop.art .Osaka) :=
  [⟨1293, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2730485921), by rfl, by decide⟩,
   ⟨1294, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3712), by rfl, by decide⟩,
   ⟨1295, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1296, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2820302411), by rfl, by decide⟩,
   ⟨1297, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3744), by rfl, by decide⟩,
   ⟨1298, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1299, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3259730800), by rfl, by decide⟩,
   ⟨1300, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3776), by rfl, by decide⟩,
   ⟨1301, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1302, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3345764771), by rfl, by decide⟩,
   ⟨1303, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3808), by rfl, by decide⟩,
   ⟨1304, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1305, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3516065817), by rfl, by decide⟩,
   ⟨1306, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3840), by rfl, by decide⟩,
   ⟨1307, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1308, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3600352804), by rfl, by decide⟩,
   ⟨1309, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3872), by rfl, by decide⟩,
   ⟨1310, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1311, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4094571909), by rfl, by decide⟩,
   ⟨1312, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3904), by rfl, by decide⟩,
   ⟨1313, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1314, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 275423344), by rfl, by decide⟩,
   ⟨1315, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3936), by rfl, by decide⟩,
   ⟨1316, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants5 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2231)
    (haw : s.activeWords = UInt256.ofNat 116)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants5Path s =
      some { s with
        pc := UInt256.ofNat 2303
        activeWords := UInt256.ofNat 124
        memory := constantMemory5 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory5, word_toNat_ofNat]
@[evmStep] def initializeConstants6Path : List (Located Loop.art .Osaka) :=
  [⟨1317, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 430227734), by rfl, by decide⟩,
   ⟨1318, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 3968), by rfl, by decide⟩,
   ⟨1319, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1320, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 506948616), by rfl, by decide⟩,
   ⟨1321, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4000), by rfl, by decide⟩,
   ⟨1322, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1323, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 659060556), by rfl, by decide⟩,
   ⟨1324, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4032), by rfl, by decide⟩,
   ⟨1325, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1326, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 883997877), by rfl, by decide⟩,
   ⟨1327, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4064), by rfl, by decide⟩,
   ⟨1328, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1329, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 958139571), by rfl, by decide⟩,
   ⟨1330, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4096), by rfl, by decide⟩,
   ⟨1331, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1332, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1322822218), by rfl, by decide⟩,
   ⟨1333, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4128), by rfl, by decide⟩,
   ⟨1334, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1335, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1537002063), by rfl, by decide⟩,
   ⟨1336, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4160), by rfl, by decide⟩,
   ⟨1337, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1338, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1747873779), by rfl, by decide⟩,
   ⟨1339, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4192), by rfl, by decide⟩,
   ⟨1340, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants6 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2303)
    (haw : s.activeWords = UInt256.ofNat 124)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants6Path s =
      some { s with
        pc := UInt256.ofNat 2375
        activeWords := UInt256.ofNat 132
        memory := constantMemory6 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory6, word_toNat_ofNat]
@[evmStep] def initializeConstants7Path : List (Located Loop.art .Osaka) :=
  [⟨1341, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 1955562222), by rfl, by decide⟩,
   ⟨1342, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4224), by rfl, by decide⟩,
   ⟨1343, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1344, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2024104815), by rfl, by decide⟩,
   ⟨1345, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4256), by rfl, by decide⟩,
   ⟨1346, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1347, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2227730452), by rfl, by decide⟩,
   ⟨1348, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4288), by rfl, by decide⟩,
   ⟨1349, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1350, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2361852424), by rfl, by decide⟩,
   ⟨1351, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4320), by rfl, by decide⟩,
   ⟨1352, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1353, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2428436474), by rfl, by decide⟩,
   ⟨1354, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4352), by rfl, by decide⟩,
   ⟨1355, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1356, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 2756734187), by rfl, by decide⟩,
   ⟨1357, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4384), by rfl, by decide⟩,
   ⟨1358, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1359, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3204031479), by rfl, by decide⟩,
   ⟨1360, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4416), by rfl, by decide⟩,
   ⟨1361, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1362, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 3329325298), by rfl, by decide⟩,
   ⟨1363, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4448), by rfl, by decide⟩,
   ⟨1364, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initializeConstants7 (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2375)
    (haw : s.activeWords = UInt256.ofNat 132)
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants7Path s =
      some { s with
        pc := UInt256.ofNat 2447
        activeWords := UInt256.ofNat 140
        memory := constantMemory7 s.memory
        stack := [n] } := by
  evm_block <;> simp [constantMemory7, word_toNat_ofNat]
@[evmStep] def initializeDriverPath : List (Located Loop.art .Osaka) :=
  [⟨1365, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1366, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 63), by rfl, by decide⟩,
   ⟨1367, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1368, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1369, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨1370, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1371, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨1372, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1373, Instr.push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨1374, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1375, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.ISZERO)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1376, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2491), by rfl, by decide⟩]

theorem run_initializeDriver (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2447)
    (haw : s.activeWords = UInt256.ofNat 140) (hstack : s.stack = [n]) :
    runLocatedBlock initializeDriverPath s =
      some { s with
        pc := UInt256.ofNat 2464
        stack := [UInt256.ofNat 2491,
          UInt256.isZero (UInt256.shiftLeft
            (UInt256.shiftRight n (UInt256.ofNat 6)) (UInt256.ofNat 6)),
          UInt256.ofNat 0,
          UInt256.shiftLeft (UInt256.shiftRight n (UInt256.ofNat 6))
            (UInt256.ofNat 6),
          UInt256.land (UInt256.ofNat 63) n, n] } := by
  evm_block
@[evmStep] def initialBranchPath : List (Located Loop.art .Osaka) :=
  [⟨1377, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPI)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_initialBranch_full (s : State) (endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2464)
    (hcond : ¬ UInt256.isTrue (UInt256.isZero endWord))
    (hstack : s.stack = [UInt256.ofNat 2491, UInt256.isZero endWord,
      UInt256.ofNat 0, endWord, rem, n] ++ rest) :
    runLocatedBlock initialBranchPath s =
      some { s with
        pc := UInt256.ofNat 2465
        stack := [UInt256.ofNat 0, endWord, rem, n] ++ rest } := by
  evm_block hcap

theorem run_initialBranch_tail (s : State) (endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2464)
    (hcond : UInt256.isTrue (UInt256.isZero endWord))
    (hstack : s.stack = [UInt256.ofNat 2491, UInt256.isZero endWord,
      UInt256.ofNat 0, endWord, rem, n] ++ rest) :
    runLocatedBlock initialBranchPath s =
      some { s with
        pc := UInt256.ofNat 2491
        stack := [UInt256.ofNat 0, endWord, rem, n] ++ rest } := by
  have hdest : Decode.isValidJumpDest Loop.bytes 2491 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 1394 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2491 = true at h
    exact h
  evm_block hcap
@[evmStep] def fullBlockCallPath : List (Located Loop.art .Osaka) :=
  [⟨1378, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1379, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1380, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1381, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨1382, Instr.op (Operation.Env (Operation.EnvOps.CALLDATACOPY)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1383, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2480), by rfl, by decide⟩,
   ⟨1384, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨1385, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMP)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_fullBlockCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullBlockCallPath s =
      some { s with
        pc := UInt256.ofNat 4
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288
        stack := [UInt256.ofNat 2480, off, endWord, rem, n] ++ rest } := by
  have hbody : Decode.isValidJumpDest Loop.bytes 4 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 2 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 4 = true at h
    exact h
  evm_block hcap
@[evmStep] def fullLoopTestPath : List (Located Loop.art .Osaka) :=
  [⟨1386, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1387, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1388, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1389, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1390, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1391, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.LT)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1392, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2465), by rfl, by decide⟩]

theorem run_fullLoopTest (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2480)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullLoopTestPath s =
      some { s with
        pc := UInt256.ofNat 2490
        stack := [UInt256.ofNat 2465,
          UInt256.lt (UInt256.ofNat 64 + off) endWord,
          UInt256.ofNat 64 + off, endWord, rem, n] ++ rest } := by
  evm_block hcap
@[evmStep] def fullLoopBranchPath : List (Located Loop.art .Osaka) :=
  [⟨1393, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPI)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_fullLoopBranch_continue (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2490)
    (hcond : UInt256.isTrue (UInt256.lt off endWord))
    (hstack : s.stack = [UInt256.ofNat 2465, UInt256.lt off endWord,
      off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullLoopBranchPath s =
      some { s with
        pc := UInt256.ofNat 2465
        stack := [off, endWord, rem, n] ++ rest } := by
  have hdest : Decode.isValidJumpDest Loop.bytes 2465 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 1378 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2465 = true at h
    exact h
  evm_block hcap

theorem run_fullLoopBranch_exit (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hpc : s.pc = UInt256.ofNat 2490)
    (hcond : ¬ UInt256.isTrue (UInt256.lt off endWord))
    (hstack : s.stack = [UInt256.ofNat 2465, UInt256.lt off endWord,
      off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullLoopBranchPath s =
      some { s with
        pc := UInt256.ofNat 2491
        stack := [off, endWord, rem, n] ++ rest } := by
  evm_block hcap
@[evmStep] def tailPreparePath : List (Located Loop.art .Osaka) :=
  [⟨1394, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1395, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨1396, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1397, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨1398, Instr.op (Operation.Env (Operation.EnvOps.CALLDATACOPY)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1399, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨1400, Instr.op (Operation.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1401, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨1402, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1403, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE8)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1404, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 56), by rfl, by decide⟩,
   ⟨1405, Instr.op (Operation.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1406, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.LT)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1407, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2533), by rfl, by decide⟩]

theorem run_tailPrepare (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hrem : rem.toNat < 64)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock tailPreparePath s =
      some { s with
        pc := UInt256.ofNat 2514
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes
          (MachineState.writeBytes s.memory
            (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288)
          (ByteArray.mk #[UInt8.ofNat
            ((UInt256.ofNat 128).toNat % 256)])
          (UInt256.ofNat 288 + rem).toNat
        stack := [UInt256.ofNat 2533,
          UInt256.lt rem (UInt256.ofNat 56), off, endWord, rem, n] ++ rest } := by
  evm_block hcap
  have hadd : (UInt256.ofNat 288 + rem).toNat = 288 + rem.toNat := by
    rw [word_toNat_add, word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    norm_num
  apply congrArg UInt256.ofNat
  norm_num [MachineState.activeWordsAfter, hadd]
  omega
@[evmStep] def tailBranchPath : List (Located Loop.art .Osaka) :=
  [⟨1408, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPI)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_tailBranch_short (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2514)
    (hcond : UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hstack : s.stack = [UInt256.ofNat 2533,
      UInt256.lt rem (UInt256.ofNat 56), off, endWord, rem, n] ++ rest) :
    runLocatedBlock tailBranchPath s =
      some { s with
        pc := UInt256.ofNat 2533
        stack := [off, endWord, rem, n] ++ rest } := by
  have hdest : Decode.isValidJumpDest Loop.bytes 2533 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 1419 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2533 = true at h
    exact h
  evm_block hcap

theorem run_tailBranch_long (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2514)
    (hcond : ¬ UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hstack : s.stack = [UInt256.ofNat 2533,
      UInt256.lt rem (UInt256.ofNat 56), off, endWord, rem, n] ++ rest) :
    runLocatedBlock tailBranchPath s =
      some { s with
        pc := UInt256.ofNat 2515
        stack := [off, endWord, rem, n] ++ rest } := by
  evm_block hcap
@[evmStep] def firstTailCallPath : List (Located Loop.art .Osaka) :=
  [⟨1409, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2522), by rfl, by decide⟩,
   ⟨1410, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨1411, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMP)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_firstTailCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2515)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock firstTailCallPath s =
      some { s with
        pc := UInt256.ofNat 4
        stack := [UInt256.ofNat 2522, off, endWord, rem, n] ++ rest } := by
  have hbody : Decode.isValidJumpDest Loop.bytes 4 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 2 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 4 = true at h
    exact h
  evm_block hcap
@[evmStep] def clearSecondTailPath : List (Located Loop.art .Osaka) :=
  [⟨1412, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1413, Instr.push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨1414, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨1415, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1416, Instr.push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨1417, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨1418, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_clearSecondTail (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2522)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock clearSecondTailPath s =
      some { s with
        pc := UInt256.ofNat 2533
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes
          (MachineState.writeBytes s.memory
            (Data.Bytes.natToBytesPadded 0 32) 288)
          (Data.Bytes.natToBytesPadded 0 32) 320 } := by
  evm_block hcap <;> simp [UInt256.toNat]
@[evmStep] def lengthCallPath : List (Located Loop.art .Osaka) :=
  [⟨1419, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1420, Instr.op (Operation.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1421, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨1422, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1423, Instr.push ⟨8, by decide⟩ (UInt256.ofNat 18446744073709551615), by rfl, by decide⟩,
   ⟨1424, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1425, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨1426, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1427, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 344), by rfl, by decide⟩,
   ⟨1428, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1429, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 2562), by rfl, by decide⟩,
   ⟨1430, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨1431, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMP)), by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_lengthCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2533)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock lengthCallPath s =
      some { s with
        pc := UInt256.ofNat 4
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded
            (UInt256.shiftLeft
              (UInt256.land (UInt256.ofNat 18446744073709551615)
                (UInt256.shiftLeft n (UInt256.ofNat 3)))
              (UInt256.ofNat 192)).toNat 32) 344
        stack := [UInt256.ofNat 2562, off, endWord, rem, n] ++ rest } := by
  have hbody : Decode.isValidJumpDest Loop.bytes 4 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 2 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 4 = true at h
    exact h
  evm_block hcap

def outputBytes (H0 H1 H2 H3 H4 H5 H6 H7 : UInt32) : ByteArray :=
  Data.Bytes.natToBytesPadded
    (UInt256.lor (ofUInt32 H7)
      (UInt256.lor (UInt256.shiftLeft (ofUInt32 H6) (UInt256.ofNat 32))
        (UInt256.lor (UInt256.shiftLeft (ofUInt32 H5) (UInt256.ofNat 64))
          (UInt256.lor (UInt256.shiftLeft (ofUInt32 H4) (UInt256.ofNat 96))
            (UInt256.lor (UInt256.shiftLeft (ofUInt32 H3) (UInt256.ofNat 128))
              (UInt256.lor (UInt256.shiftLeft (ofUInt32 H2) (UInt256.ofNat 160))
                (UInt256.lor (UInt256.shiftLeft (ofUInt32 H1) (UInt256.ofNat 192))
                  (UInt256.shiftLeft (ofUInt32 H0) (UInt256.ofNat 224))))))))).toNat 32

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverBlocks
