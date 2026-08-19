import Challenge.Sha256.Submissions.Sha256Fast.Proofs.Rounds8
set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
set_option linter.unusedVariables false

/-! One iteration of the schedule loop of the loop-of-8 SHA-256 artifact,
proved as a single block. -/

namespace Loop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word Challenge.Sha256.Fast
open EvmSemantics.Crypto.Sha256
private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
@[evmStep] def psched_costStep0 : List (Located art .Osaka) :=
  [⟨133, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨134, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 832), by rfl, by decide⟩,
   ⟨135, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨136, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨137, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨138, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨139, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨140, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨141, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨142, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨143, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨144, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨145, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨146, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨147, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨148, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨149, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨150, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨151, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨152, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨153, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨154, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨155, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨156, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨157, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨158, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨159, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨160, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨161, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨162, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨163, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 672), by rfl, by decide⟩,
   ⟨164, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨165, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨166, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨167, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨168, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 384), by rfl, by decide⟩,
   ⟨169, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨170, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨171, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨172, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨173, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨174, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨175, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨176, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨177, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 896), by rfl, by decide⟩,
   ⟨178, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costStep1 : List (Located art .Osaka) :=
  [⟨180, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨181, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 864), by rfl, by decide⟩,
   ⟨182, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨183, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨184, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨185, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨186, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨187, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨188, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨189, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨190, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨191, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨192, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨193, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨194, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨195, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨196, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨197, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨198, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨199, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨200, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨201, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨202, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨203, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨204, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨205, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨206, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨207, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨208, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨209, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨210, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 704), by rfl, by decide⟩,
   ⟨211, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨212, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨213, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨214, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨215, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨216, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨217, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨218, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨219, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨220, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨221, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨222, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨223, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨224, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 928), by rfl, by decide⟩,
   ⟨225, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨226, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costStep2 : List (Located art .Osaka) :=
  [⟨227, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨228, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 896), by rfl, by decide⟩,
   ⟨229, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨230, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨231, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨232, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨233, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨234, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨235, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨236, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨237, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨238, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨239, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨240, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨241, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨242, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨243, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨244, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨245, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨246, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨247, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨248, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨249, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨250, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨251, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨252, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨253, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨254, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨255, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨256, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨257, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 736), by rfl, by decide⟩,
   ⟨258, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨259, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨260, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨261, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨262, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨263, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨264, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨265, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨266, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨267, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨268, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨269, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨270, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨271, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 960), by rfl, by decide⟩,
   ⟨272, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨273, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costStep3 : List (Located art .Osaka) :=
  [⟨274, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨275, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 928), by rfl, by decide⟩,
   ⟨276, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨277, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨278, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨279, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨280, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨281, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨282, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨283, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨284, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨285, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨286, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨287, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨288, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨289, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨290, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨291, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨292, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨293, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨294, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨295, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨296, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨297, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨298, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨299, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨300, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨301, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨302, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨303, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨304, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 768), by rfl, by decide⟩,
   ⟨305, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨306, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨307, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨308, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨309, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨310, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨311, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨312, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨313, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨314, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨315, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨316, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨317, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨318, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨319, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨320, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costStep4 : List (Located art .Osaka) :=
  [⟨321, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨322, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 960), by rfl, by decide⟩,
   ⟨323, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨324, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨325, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨326, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨327, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨328, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨329, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨330, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨331, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨332, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨333, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨334, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨335, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨336, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨337, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨338, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨339, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨340, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨341, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨342, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨343, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨344, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨345, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨346, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨348, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨349, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨350, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨351, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨352, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨353, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨354, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨355, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨356, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨357, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨358, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨359, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨360, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨361, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨362, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨363, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨364, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨365, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1024), by rfl, by decide⟩,
   ⟨366, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨367, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costStep5 : List (Located art .Osaka) :=
  [⟨368, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨369, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨370, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨371, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨372, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨373, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨374, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨375, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨376, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨377, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨378, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨379, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨380, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨381, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨382, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨383, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 576), by rfl, by decide⟩,
   ⟨384, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨385, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨386, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨387, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨388, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨389, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨390, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨391, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨392, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨393, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨394, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨395, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨396, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨397, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨398, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 832), by rfl, by decide⟩,
   ⟨399, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨400, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨401, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨402, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨403, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨404, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨405, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨406, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨407, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨408, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨409, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨410, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨411, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨412, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨413, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨414, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costStep6 : List (Located art .Osaka) :=
  [⟨415, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨416, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1024), by rfl, by decide⟩,
   ⟨417, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨418, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨419, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨420, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨421, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨422, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨423, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨424, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨425, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨426, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨427, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨428, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨429, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨430, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 608), by rfl, by decide⟩,
   ⟨431, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨432, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨433, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨434, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨435, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨436, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨437, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨438, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨439, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨440, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨441, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨442, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨443, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨444, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨445, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 864), by rfl, by decide⟩,
   ⟨446, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨447, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨448, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨449, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨450, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 576), by rfl, by decide⟩,
   ⟨451, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨452, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨453, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨454, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨455, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨456, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨457, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨458, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨459, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1088), by rfl, by decide⟩,
   ⟨460, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨461, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costStep7 : List (Located art .Osaka) :=
  [⟨462, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨463, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨464, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨465, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨466, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨467, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨468, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨469, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨470, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨471, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨472, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨473, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨474, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨475, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨476, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨477, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 640), by rfl, by decide⟩,
   ⟨478, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨479, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨480, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨481, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨482, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨483, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨484, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨485, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨486, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨487, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨488, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨489, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨490, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨491, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨492, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 896), by rfl, by decide⟩,
   ⟨493, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨494, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨495, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨496, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨497, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 608), by rfl, by decide⟩,
   ⟨498, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨499, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨500, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨501, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨502, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨503, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨504, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨505, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨506, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1120), by rfl, by decide⟩,
   ⟨507, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨508, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩]
@[evmStep] def psched_costControlSetup : List (Located art .Osaka) :=
  [⟨509, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨510, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨511, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1536), by rfl, by decide⟩,
   ⟨512, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨513, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.LT)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨514, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 294), by rfl, by decide⟩]
@[evmStep] def psched_compute : List (Located art .Osaka) :=
  [⟨133, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨134, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 832), by rfl, by decide⟩,
   ⟨135, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨136, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨137, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨138, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨139, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨140, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨141, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨142, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨143, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨144, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨145, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨146, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨147, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨148, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨149, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨150, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨151, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨152, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨153, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨154, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨155, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨156, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨157, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨158, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨159, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨160, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨161, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨162, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨163, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 672), by rfl, by decide⟩,
   ⟨164, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨165, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨166, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨167, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨168, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 384), by rfl, by decide⟩,
   ⟨169, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨170, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨171, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨172, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨173, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨174, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨175, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨176, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨177, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 896), by rfl, by decide⟩,
   ⟨178, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨180, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨181, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 864), by rfl, by decide⟩,
   ⟨182, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨183, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨184, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨185, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨186, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨187, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨188, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨189, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨190, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨191, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨192, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨193, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨194, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨195, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨196, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨197, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨198, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨199, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨200, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨201, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨202, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨203, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨204, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨205, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨206, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨207, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨208, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨209, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨210, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 704), by rfl, by decide⟩,
   ⟨211, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨212, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨213, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨214, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨215, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨216, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨217, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨218, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨219, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨220, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨221, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨222, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨223, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨224, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 928), by rfl, by decide⟩,
   ⟨225, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨226, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨227, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨228, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 896), by rfl, by decide⟩,
   ⟨229, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨230, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨231, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨232, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨233, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨234, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨235, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨236, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨237, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨238, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨239, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨240, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨241, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨242, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨243, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨244, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨245, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨246, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨247, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨248, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨249, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨250, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨251, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨252, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨253, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨254, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨255, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨256, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨257, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 736), by rfl, by decide⟩,
   ⟨258, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨259, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨260, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨261, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨262, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨263, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨264, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨265, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨266, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨267, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨268, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨269, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨270, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨271, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 960), by rfl, by decide⟩,
   ⟨272, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨273, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨274, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨275, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 928), by rfl, by decide⟩,
   ⟨276, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨277, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨278, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨279, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨280, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨281, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨282, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨283, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨284, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨285, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨286, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨287, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨288, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨289, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨290, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨291, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨292, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨293, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨294, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨295, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨296, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨297, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨298, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨299, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨300, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨301, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨302, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨303, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨304, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 768), by rfl, by decide⟩,
   ⟨305, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨306, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨307, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨308, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨309, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨310, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨311, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨312, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨313, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨314, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨315, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨316, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨317, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨318, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨319, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨320, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨321, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨322, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 960), by rfl, by decide⟩,
   ⟨323, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨324, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨325, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨326, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨327, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨328, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨329, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨330, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨331, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨332, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨333, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨334, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨335, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨336, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨337, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨338, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨339, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨340, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨341, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨342, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨343, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨344, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨345, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨346, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨348, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨349, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨350, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨351, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨352, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨353, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨354, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨355, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨356, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨357, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨358, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨359, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨360, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨361, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨362, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨363, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨364, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨365, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1024), by rfl, by decide⟩,
   ⟨366, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨367, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨368, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨369, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 992), by rfl, by decide⟩,
   ⟨370, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨371, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨372, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨373, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨374, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨375, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨376, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨377, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨378, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨379, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨380, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨381, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨382, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨383, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 576), by rfl, by decide⟩,
   ⟨384, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨385, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨386, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨387, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨388, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨389, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨390, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨391, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨392, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨393, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨394, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨395, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨396, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨397, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨398, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 832), by rfl, by decide⟩,
   ⟨399, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨400, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨401, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨402, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨403, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨404, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨405, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨406, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨407, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨408, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨409, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨410, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨411, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨412, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨413, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨414, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨415, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨416, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1024), by rfl, by decide⟩,
   ⟨417, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨418, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨419, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨420, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨421, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨422, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨423, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨424, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨425, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨426, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨427, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨428, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨429, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨430, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 608), by rfl, by decide⟩,
   ⟨431, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨432, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨433, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨434, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨435, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨436, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨437, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨438, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨439, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨440, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨441, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨442, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨443, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨444, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨445, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 864), by rfl, by decide⟩,
   ⟨446, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨447, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨448, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨449, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨450, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 576), by rfl, by decide⟩,
   ⟨451, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨452, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨453, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨454, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨455, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨456, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨457, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨458, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨459, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1088), by rfl, by decide⟩,
   ⟨460, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨461, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨462, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨463, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨464, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨465, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨466, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨467, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨468, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨469, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨470, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨471, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨472, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 23), by rfl, by decide⟩,
   ⟨473, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨474, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨475, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨476, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨477, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 640), by rfl, by decide⟩,
   ⟨478, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨479, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨480, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨481, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨482, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨483, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨484, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨485, Instr.op (Operation.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨486, Instr.push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨487, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.SHR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨488, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨489, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.XOR)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨490, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨491, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨492, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 896), by rfl, by decide⟩,
   ⟨493, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨494, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨495, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨496, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨497, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 608), by rfl, by decide⟩,
   ⟨498, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨499, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨500, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨501, Instr.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨502, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.AND)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨503, Instr.push ⟨5, by decide⟩ (UInt256.ofNat 4294967297), by rfl, by decide⟩,
   ⟨504, Instr.op (Operation.StopArith (Operation.StopArithOps.MUL)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨505, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨506, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1120), by rfl, by decide⟩,
   ⟨507, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨508, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨509, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨510, Instr.op (Operation.StopArith (Operation.StopArithOps.ADD)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨511, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 1536), by rfl, by decide⟩,
   ⟨512, Instr.op (Operation.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨513, Instr.op (Operation.CompBit (Operation.CompareBitwiseOps.LT)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨514, Instr.push ⟨2, by decide⟩ (UInt256.ofNat 294), by rfl, by decide⟩]
@[evmStep] def psched_branch : List (Located art .Osaka) :=
  [⟨515, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPI)), by rfl, wfOp (by decide) trivial rfl⟩]

/-- One iteration of the schedule loop, through the branch setup:
the eight W slots of the group are computed and stored from the sixteen
preceding slots, all addresses relative to the group pointer `u`. -/
theorem sched_iter_compute (s : State)
    (V14 V9 V1 V0 V15 V10 V2 V11 V3 V12 V4 V13 V5 V6 V7 V8 : UInt32)
    (u : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hu : u.toNat ≤ 1280)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 295)
    (hstack : s.stack = u :: rest)
    (hv14 : MachineState.readWord s.memory
      (UInt256.ofNat 832 + u).toNat = dbl (ofUInt32 V14))
    (hv9 : MachineState.readWord s.memory
      (UInt256.ofNat 672 + u).toNat = dbl (ofUInt32 V9))
    (hv1 : MachineState.readWord s.memory
      (UInt256.ofNat 416 + u).toNat = dbl (ofUInt32 V1))
    (hv0 : MachineState.readWord s.memory
      (UInt256.ofNat 384 + u).toNat = dbl (ofUInt32 V0))
    (hv15 : MachineState.readWord s.memory
      (UInt256.ofNat 864 + u).toNat = dbl (ofUInt32 V15))
    (hv10 : MachineState.readWord s.memory
      (UInt256.ofNat 704 + u).toNat = dbl (ofUInt32 V10))
    (hv2 : MachineState.readWord s.memory
      (UInt256.ofNat 448 + u).toNat = dbl (ofUInt32 V2))
    (hv11 : MachineState.readWord s.memory
      (UInt256.ofNat 736 + u).toNat = dbl (ofUInt32 V11))
    (hv3 : MachineState.readWord s.memory
      (UInt256.ofNat 480 + u).toNat = dbl (ofUInt32 V3))
    (hv12 : MachineState.readWord s.memory
      (UInt256.ofNat 768 + u).toNat = dbl (ofUInt32 V12))
    (hv4 : MachineState.readWord s.memory
      (UInt256.ofNat 512 + u).toNat = dbl (ofUInt32 V4))
    (hv13 : MachineState.readWord s.memory
      (UInt256.ofNat 800 + u).toNat = dbl (ofUInt32 V13))
    (hv5 : MachineState.readWord s.memory
      (UInt256.ofNat 544 + u).toNat = dbl (ofUInt32 V5))
    (hv6 : MachineState.readWord s.memory
      (UInt256.ofNat 576 + u).toNat = dbl (ofUInt32 V6))
    (hv7 : MachineState.readWord s.memory
      (UInt256.ofNat 608 + u).toNat = dbl (ofUInt32 V7))
    (hv8 : MachineState.readWord s.memory
      (UInt256.ofNat 640 + u).toNat = dbl (ofUInt32 V8)) :
    runLocatedBlock psched_compute s =
      some { s with
        pc := UInt256.ofNat 883
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 V14 + V9 + smallSigma0 V1 + V0))).toNat 32)
          (UInt256.ofNat 896 + u).toNat)
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 V15 + V10 + smallSigma0 V2 + V1))).toNat 32)
          (UInt256.ofNat 928 + u).toNat)
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 (smallSigma1 V14 + V9 + smallSigma0 V1 + V0) + V11 + smallSigma0 V3 + V2))).toNat 32)
          (UInt256.ofNat 960 + u).toNat)
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 (smallSigma1 V15 + V10 + smallSigma0 V2 + V1) + V12 + smallSigma0 V4 + V3))).toNat 32)
          (UInt256.ofNat 992 + u).toNat)
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 (smallSigma1 (smallSigma1 V14 + V9 + smallSigma0 V1 + V0) + V11 + smallSigma0 V3 + V2) + V13 + smallSigma0 V5 + V4))).toNat 32)
          (UInt256.ofNat 1024 + u).toNat)
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 (smallSigma1 (smallSigma1 V15 + V10 + smallSigma0 V2 + V1) + V12 + smallSigma0 V4 + V3) + V14 + smallSigma0 V6 + V5))).toNat 32)
          (UInt256.ofNat 1056 + u).toNat)
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 (smallSigma1 (smallSigma1 (smallSigma1 V14 + V9 + smallSigma0 V1 + V0) + V11 + smallSigma0 V3 + V2) + V13 + smallSigma0 V5 + V4) + V15 + smallSigma0 V7 + V6))).toNat 32)
          (UInt256.ofNat 1088 + u).toNat)
          (Data.Bytes.natToBytesPadded (dbl (ofUInt32 (smallSigma1 (smallSigma1 (smallSigma1 (smallSigma1 V15 + V10 + smallSigma0 V2 + V1) + V12 + smallSigma0 V4 + V3) + V14 + smallSigma0 V6 + V5) + (smallSigma1 V14 + V9 + smallSigma0 V1 + V0) + smallSigma0 V8 + V7))).toNat 32)
          (UInt256.ofNat 1120 + u).toNat
        stack := [UInt256.ofNat 294, UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536), UInt256.ofNat 256 + u] ++ rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + u).toNat = k + u.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hb384 : (UInt256.ofNat 384 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 384 (by omega)]; omega
  have hb416 : (UInt256.ofNat 416 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 416 (by omega)]; omega
  have hb448 : (UInt256.ofNat 448 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 448 (by omega)]; omega
  have hb480 : (UInt256.ofNat 480 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 480 (by omega)]; omega
  have hb512 : (UInt256.ofNat 512 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 512 (by omega)]; omega
  have hb544 : (UInt256.ofNat 544 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 544 (by omega)]; omega
  have hb576 : (UInt256.ofNat 576 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 576 (by omega)]; omega
  have hb608 : (UInt256.ofNat 608 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 608 (by omega)]; omega
  have hb640 : (UInt256.ofNat 640 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 640 (by omega)]; omega
  have hb672 : (UInt256.ofNat 672 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 672 (by omega)]; omega
  have hb704 : (UInt256.ofNat 704 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 704 (by omega)]; omega
  have hb736 : (UInt256.ofNat 736 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 736 (by omega)]; omega
  have hb768 : (UInt256.ofNat 768 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 768 (by omega)]; omega
  have hb800 : (UInt256.ofNat 800 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 800 (by omega)]; omega
  have hb832 : (UInt256.ofNat 832 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 832 (by omega)]; omega
  have hb864 : (UInt256.ofNat 864 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 864 (by omega)]; omega
  have hb896 : (UInt256.ofNat 896 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 896 (by omega)]; omega
  have hb928 : (UInt256.ofNat 928 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 928 (by omega)]; omega
  have hb960 : (UInt256.ofNat 960 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 960 (by omega)]; omega
  have hb992 : (UInt256.ofNat 992 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 992 (by omega)]; omega
  have hb1024 : (UInt256.ofNat 1024 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 1024 (by omega)]; omega
  have hb1056 : (UInt256.ofNat 1056 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 1056 (by omega)]; omega
  have hb1088 : (UInt256.ofNat 1088 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 1088 (by omega)]; omega
  have hb1120 : (UInt256.ofNat 1120 + u).toNat + 32 ≤ 4480 := by
    rw [hoff 1120 (by omega)]; omega
  clear hoff
  evm_block hcap
  and_intros <;>
    first
    | rfl
    | ac_rfl
    | omega
    | (repeat' first
        | rfl
        | (apply congrArg₂ (fun x y => MachineState.writeBytes x y _))
        | (apply congrArg (fun n => Data.Bytes.natToBytesPadded n 32))
        | (apply congrArg UInt256.toNat)
        | (apply congrArg dbl)
        | (apply congrArg ofUInt32)
        | ac_rfl)

/-- Take the schedule-loop back edge after a non-final group. -/
theorem sched_branch_continue (s : State) (u : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = bytes) (hrun : s.halt = .Running)
    (hpc : s.pc = UInt256.ofNat 883)
    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536)))
    (hstack : s.stack =
      [UInt256.ofNat 294,
       UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536),
       UInt256.ofNat 256 + u] ++ rest) :
    runLocatedBlock psched_branch s =
      some { s with
        pc := UInt256.ofNat 294
        stack := (UInt256.ofNat 256 + u) :: rest } := by
  have hdest : Decode.isValidJumpDest bytes 294 = true := by
    have h := ProgramArtifact.isValidJumpDest_index art 132 (by rfl)
    have hpcd : art.instructionPC 132 = 294 := by rfl
    rw [hpcd] at h
    exact h
  evm_block hcap

/-- Fall through after the sixth and final schedule group. -/
theorem sched_branch_exit (s : State) (u : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running)
    (hpc : s.pc = UInt256.ofNat 883)
    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536)) = false)
    (hstack : s.stack =
      [UInt256.ofNat 294,
       UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536),
       UInt256.ofNat 256 + u] ++ rest) :
    runLocatedBlock psched_branch s =
      some { s with
        pc := UInt256.ofNat 884
        stack := (UInt256.ofNat 256 + u) :: rest } := by
  evm_block hcap

end Loop
