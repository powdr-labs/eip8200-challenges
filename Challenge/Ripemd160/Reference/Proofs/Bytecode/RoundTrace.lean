import Challenge.Ripemd160.Reference.Proofs.Bytecode.TableTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.BooleanFunctionTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Compression
import YulEvmCompiler.LowerDefs

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Direct trace of the RIPEMD-160 round helper

The six straight-line pieces below are exactly artifact indices 208 through
312.  The intervening calls reuse the certified `xAt`, Boolean-function, and
word-store paths.  A local copy of the `rotl` path is used while the shared
`Functions` module is being migrated to the current stepper interface.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.RoundTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka

def prefixPath : List Located :=
  [⟨208, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨209, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨210, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨211, .push ⟨1, by decide⟩ (UInt256.ofNat 0x20), by rfl, by decide⟩,
   ⟨212, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨213, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨214, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨215, .push ⟨1, by decide⟩ (UInt256.ofNat 0x40), by rfl, by decide⟩,
   ⟨216, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨217, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨218, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨219, .push ⟨1, by decide⟩ (UInt256.ofNat 0x60), by rfl, by decide⟩,
   ⟨220, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨221, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨222, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨223, .push ⟨1, by decide⟩ (UInt256.ofNat 0x80), by rfl, by decide⟩,
   ⟨224, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨225, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨226, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨227, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨228, .op (.Dup ⟨10, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨229, .push ⟨2, by decide⟩ (UInt256.ofNat 0x13a), by rfl, by decide⟩,
   ⟨230, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨231, .op (.Dup ⟨11, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨232, .push ⟨2, by decide⟩ (UInt256.ofNat 0x4b), by rfl, by decide⟩,
   ⟨233, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def afterXPath : List Located :=
  [⟨234, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨235, .push ⟨2, by decide⟩ (UInt256.ofNat 0x147), by rfl, by decide⟩,
   ⟨236, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨237, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨238, .op (.Dup ⟨8, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨239, .op (.Dup ⟨10, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨240, .op (.Dup ⟨14, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨241, .push ⟨2, by decide⟩ (UInt256.ofNat 0x93), by rfl, by decide⟩,
   ⟨242, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def afterFPath : List Located :=
  [⟨243, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨244, .op (.Dup ⟨8, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨245, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨246, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨247, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨248, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨249, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨250, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨251, .push ⟨2, by decide⟩ (UInt256.ofNat 0x15d), by rfl, by decide⟩,
   ⟨252, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨253, .op (.Dup ⟨13, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨254, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨255, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨256, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def afterRot1Path : List Located :=
  [⟨257, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨258, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨259, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨260, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨261, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨262, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨263, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨264, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨265, .op (.Dup ⟨7, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨266, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨267, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨268, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨269, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨270, .push ⟨1, by decide⟩ (UInt256.ofNat 0x80), by rfl, by decide⟩,
   ⟨271, .op (.Dup ⟨8, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨272, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨273, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨274, .push ⟨2, by decide⟩ (UInt256.ofNat 0x18d), by rfl, by decide⟩,
   ⟨275, .push ⟨2, by decide⟩ (UInt256.ofNat 0x185), by rfl, by decide⟩,
   ⟨276, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨277, .push ⟨1, by decide⟩ (UInt256.ofNat 10), by rfl, by decide⟩,
   ⟨278, .op (.Dup ⟨7, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨279, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨280, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def afterRot2Path : List Located :=
  [⟨281, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨282, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨283, .op (.Dup ⟨9, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨284, .push ⟨2, by decide⟩ (UInt256.ofNat 0x33), by rfl, by decide⟩,
   ⟨285, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def suffixPath : List Located :=
  [⟨286, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨287, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨288, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨289, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨290, .push ⟨1, by decide⟩ (UInt256.ofNat 0x40), by rfl, by decide⟩,
   ⟨291, .op (.Dup ⟨8, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨292, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨293, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨294, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨295, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨296, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨297, .push ⟨1, by decide⟩ (UInt256.ofNat 0x20), by rfl, by decide⟩,
   ⟨298, .op (.Dup ⟨8, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨299, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨300, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨301, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨302, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨303, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨304, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨305, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨306, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨307, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨308, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨309, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨310, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨311, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨312, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

private def roundPCs : List Nat :=
  [276, 277, 278, 279, 281, 282, 283, 284, 286, 287, 288, 289,
   291, 292, 293, 294, 296, 297, 298, 299, 304, 305, 308, 309,
   310, 313, 314, 315, 318, 319, 320, 321, 322, 323, 326, 327,
   328, 329, 330, 331, 332, 333, 338, 339, 342, 343, 344, 345,
   348, 349, 350, 351, 352, 353, 354, 359, 360, 361, 362, 363,
   368, 369, 370, 372, 373, 374, 375, 378, 381, 382, 384, 385,
   388, 389, 390, 392, 393, 396, 397, 398, 403, 404, 405, 407,
   408, 409, 410, 415, 416, 417, 419, 420, 421, 422, 423, 424,
   425, 426, 427, 428, 429, 430, 431, 432, 433]

@[simp] private theorem roundRefPC (i : Nat) (hlo : 208 ≤ i) (hhi : i ≤ 312) :
    Artifact.referenceArtifact.instructionPC i = roundPCs[i - 208]! := by
  interval_cases i <;> rfl

/-! The compiler calls the same `rotl` helper twice in every round. -/

def rotlPath : List Located :=
  [⟨2, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨4, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨5, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨7, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨8, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨9, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨10, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨11, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨12, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨13, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨14, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨15, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨16, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨17, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨18, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨19, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Complete dynamic instruction path through one `round` invocation. -/
def roundTracePath (j : Nat) : List Located :=
  prefixPath ++ TableTrace.xAtPath ++ afterXPath ++
    BooleanFunctionTrace.casePath j ++ afterFPath ++ rotlPath ++
    afterRot1Path ++ rotlPath ++ afterRot2Path ++ TableTrace.hSetPath ++
    suffixPath

private def rotlValue (x n : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.lor (UInt256.shiftLeft x n)
      (UInt256.shiftRight x (UInt256.ofNat 32 - n)))
    (UInt256.ofNat 0xffffffff)

def rotlEntry (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4
           stack := [x, n, 0, returnDest] ++ rest }

def rotlReturned (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := rotlValue x n :: rest }

@[simp] private theorem rotlRefPC (i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ 19) :
    Artifact.referenceArtifact.instructionPC i =
      [4, 5, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26][i - 2]! := by
  interval_cases i <;> rfl

set_option linter.unusedSimpArgs false in
theorem run_rotl (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotlPath
      (rotlEntry s x n returnDest rest) =
        some (rotlReturned s x n returnDest rest) := by
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  have hswap4 (a b c d : UInt256) (rho : List UInt256) :
      (a :: b :: c :: d :: rho).exchange 0 3 =
        some (d :: b :: c :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a d [b, c] rho
  have hswap2 (a b : UInt256) (rho : List UInt256) :
      (a :: b :: rho).exchange 0 1 = some (b :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a b ([] : List UInt256) rho
  simp (config := { maxSteps := 200000 })
    [rotlPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rotlEntry, rotlReturned, rotlValue, Challenge.EvmProof.Word.mask32,
      hrun, hcode, hvalid, hcap, hswap4, hswap2, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

def gasSteps_rotl (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (rotlEntry s x n returnDest rest)
      (rotlReturned s x n returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka rotlPath
      (s := rotlEntry s x n returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_rotl s x n returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

/-! ## Caller-visible states and the six owned blocks -/

def roundEntry (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x114
           stack := [base, UInt256.ofNat j, wordIndex, rotation, k,
             returnDest] ++ rest }

def loadedA (s : State) (base : UInt256) : UInt256 :=
  MachineState.readWord s.memory base.toNat

def loadedB (s : State) (base : UInt256) : UInt256 :=
  MachineState.readWord s.memory (base + UInt256.ofNat 0x20).toNat

def loadedC (s : State) (base : UInt256) : UInt256 :=
  MachineState.readWord s.memory (base + UInt256.ofNat 0x40).toNat

def loadedD (s : State) (base : UInt256) : UInt256 :=
  MachineState.readWord s.memory (base + UInt256.ofNat 0x60).toNat

def loadedE (s : State) (base : UInt256) : UInt256 :=
  MachineState.readWord s.memory (base + UInt256.ofNat 0x80).toNat

private def afterLoads (s : State) (base : UInt256) : State :=
  let s := { s with activeWords := (s.activeWordsAfterUInt256 base.toNat 32) }
  let s := { s with activeWords := (s.activeWordsAfterUInt256
    (base + UInt256.ofNat 0x20).toNat 32) }
  let s := { s with activeWords := (s.activeWordsAfterUInt256
    (base + UInt256.ofNat 0x40).toNat 32) }
  let s := { s with activeWords := (s.activeWordsAfterUInt256
    (base + UInt256.ofNat 0x60).toNat 32) }
  { s with activeWords := (s.activeWordsAfterUInt256
    (base + UInt256.ofNat 0x80).toNat 32) }

private def roundTail (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [k, UInt256.ofNat 0xffffffff, loadedE s base, loadedD s base,
    loadedC s base, loadedB s base, loadedA s base, base, UInt256.ofNat j,
    wordIndex, rotation, k, returnDest] ++ rest

def xCallState (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256) : State :=
  TableTrace.atEntry (afterLoads s base) (UInt256.ofNat 0x4b) wordIndex
    (UInt256.ofNat 0x13a)
    (roundTail s base j wordIndex rotation k returnDest rest)

private def xReturnedState (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256) : State :=
  TableTrace.atReturned (afterLoads s base) (UInt256.ofNat 0x2a0) wordIndex
    (UInt256.ofNat 0x13a)
    (roundTail s base j wordIndex rotation k returnDest rest)

private def fTail (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [word, k, UInt256.ofNat 0xffffffff, loadedE s base, loadedD s base,
    loadedC s base, loadedB s base, loadedA s base, base, UInt256.ofNat j,
    wordIndex, rotation, k, returnDest] ++ rest

def fCallState (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) : State :=
  BooleanFunctionTrace.fEntry s j (loadedB s base) (loadedC s base)
    (loadedD s base) (UInt256.ofNat 0x147)
    (fTail s base j wordIndex rotation k returnDest word rest)

private def t0 (s : State) (base : UInt256) (j : Nat)
    (word k : UInt256) : UInt256 :=
  UInt256.land
    (((loadedA s base + Word.evmF j (loadedB s base) (loadedC s base)
      (loadedD s base)) + word) + k) (UInt256.ofNat 0xffffffff)

private def rot1Tail (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [loadedE s base, UInt256.ofNat 0xffffffff, t0 s base j word k,
    loadedE s base, loadedD s base, loadedC s base, loadedB s base,
    loadedA s base, base, UInt256.ofNat j, wordIndex, rotation, k,
    returnDest] ++ rest

def rot1CallState (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) : State :=
  rotlEntry s (t0 s base j word k) rotation (UInt256.ofNat 0x15d)
    (rot1Tail s base j wordIndex rotation k returnDest word rest)

private def nextB (s : State) (base : UInt256) (j : Nat)
    (word rotation k : UInt256) : UInt256 :=
  UInt256.land (rotlValue (t0 s base j word k) rotation + loadedE s base)
    (UInt256.ofNat 0xffffffff)

private def afterFirstStores (s : State) (base : UInt256) : State :=
  TableTrace.storedWord
    (TableTrace.storedWord s base (UInt256.ofNat 0) (loadedE s base))
    base (UInt256.ofNat 4) (loadedD s base)

private def rot2Tail (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [UInt256.ofNat 0x18d, nextB s base j word rotation k, loadedE s base,
    loadedD s base, loadedC s base, loadedB s base, loadedA s base, base,
    UInt256.ofNat j, wordIndex, rotation, k, returnDest] ++ rest

def rot2CallState (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) : State :=
  rotlEntry (afterFirstStores s base) (loadedC s base) (UInt256.ofNat 10)
    (UInt256.ofNat 0x185)
    (rot2Tail s base j wordIndex rotation k returnDest word rest)

private def setTail (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [nextB s base j word rotation k, loadedE s base, loadedD s base,
    loadedC s base, loadedB s base, loadedA s base, base, UInt256.ofNat j,
    wordIndex, rotation, k, returnDest] ++ rest

def setCallState (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (rest : List UInt256) : State :=
  TableTrace.setEntry (afterFirstStores s base) base (UInt256.ofNat 3)
    (rotlValue (loadedC s base) (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
    (setTail s base j wordIndex rotation k returnDest word rest)

@[simp] private theorem valid4 :
    Decode.isValidJumpDest referenceBytecode 4 = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 2 (by rfl)

@[simp] private theorem valid33 :
    Decode.isValidJumpDest referenceBytecode 0x33 = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 38 (by rfl)

@[simp] private theorem valid4B :
    Decode.isValidJumpDest referenceBytecode 0x4b = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 55 (by rfl)

@[simp] private theorem valid93 :
    Decode.isValidJumpDest referenceBytecode 0x93 = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 108 (by rfl)

@[simp] private theorem valid13A :
    Decode.isValidJumpDest referenceBytecode 0x13a = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 234 (by rfl)

@[simp] private theorem valid147 :
    Decode.isValidJumpDest referenceBytecode 0x147 = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 243 (by rfl)

@[simp] private theorem valid15D :
    Decode.isValidJumpDest referenceBytecode 0x15d = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 257 (by rfl)

@[simp] private theorem valid185 :
    Decode.isValidJumpDest referenceBytecode 0x185 = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 281 (by rfl)

@[simp] private theorem valid18D :
    Decode.isValidJumpDest referenceBytecode 0x18d = true := by
  exact Artifact.referenceArtifact.isValidJumpDest_index 286 (by rfl)

private theorem cap (rest : List UInt256) (h : rest.length < 980)
    (n : Nat) (hn : n ≤ 40) : rest.length + n < 1024 := by omega

private theorem swap2 (a b : UInt256) (rho : List UInt256) :
    (a :: b :: rho).exchange 0 1 = some (b :: a :: rho) := by
  simpa using YulEvmCompiler.exchange_swap a b ([] : List UInt256) rho

@[simp] private theorem smallAdd (a b : Nat) (ha : a ≤ 500) (hb : b ≤ 5) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)

@[simp] private theorem smallSucc (a : Nat) (ha : a ≤ 500) :
    (UInt256.ofNat a).succ = UInt256.ofNat (a + 1) := by
  exact Challenge.EvmProof.Word.succ_ofNat (by omega)

@[simp] private theorem smallToNat (a : Nat) (ha : a ≤ 500) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[simp] private theorem slot0 (base : UInt256) :
    TableTrace.slotAddress base (0 : UInt256) = base := by
  rw [TableTrace.slotAddress]
  have hz : UInt256.shiftLeft (0 : UInt256) (UInt256.ofNat 5) =
      UInt256.ofNat 0 := by decide
  rw [hz]
  apply Challenge.EvmProof.Word.word_ext
  change ((UInt256.ofNat 0).val + base.val).val = base.val.val
  rw [Fin.val_add]
  have hz : (UInt256.ofNat 0).val.val = 0 := by decide
  rw [hz, Nat.zero_add, Nat.mod_eq_of_lt base.val.isLt]

@[simp] private theorem explicitZero :
    UInt256.ofNat 0 = (0 : UInt256) := by rfl

@[simp] private theorem slot1 (base : UInt256) :
    TableTrace.slotAddress base (UInt256.ofNat 1) =
      base + UInt256.ofNat 0x20 := by
  rw [TableTrace.slotAddress,
    Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
      (by norm_num)]
  exact Challenge.EvmProof.Word.word_add_comm _ _

@[simp] private theorem slot2 (base : UInt256) :
    TableTrace.slotAddress base (UInt256.ofNat 2) =
      base + UInt256.ofNat 0x40 := by
  rw [TableTrace.slotAddress,
    Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
      (by norm_num)]
  exact Challenge.EvmProof.Word.word_add_comm _ _

@[simp] private theorem slot3 (base : UInt256) :
    TableTrace.slotAddress base (UInt256.ofNat 3) =
      base + UInt256.ofNat 0x60 := by
  rw [TableTrace.slotAddress,
    Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
      (by norm_num)]
  exact Challenge.EvmProof.Word.word_add_comm _ _

@[simp] private theorem slot4 (base : UInt256) :
    TableTrace.slotAddress base (UInt256.ofNat 4) =
      base + UInt256.ofNat 0x80 := by
  rw [TableTrace.slotAddress,
    Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
      (by norm_num)]
  exact Challenge.EvmProof.Word.word_add_comm _ _

set_option linter.unusedSimpArgs false in
theorem run_prefix (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 980)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock prefixPath
      (roundEntry s base j wordIndex rotation k returnDest rest) =
        some (xCallState s base j wordIndex rotation k returnDest rest) := by
  simp (config := { maxSteps := 300000 })
    [prefixPath, roundPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      roundEntry, xCallState, TableTrace.atEntry, afterLoads, roundTail,
      loadedA, loadedB, loadedC, loadedD, loadedE,
      hrun, hcode, cap rest hstack, Nat.add_assoc,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

private def genericTail (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [k, UInt256.ofNat 0xffffffff, e, d, c, b, a, base, UInt256.ofNat j,
    wordIndex, rotation, k, returnDest] ++ rest

private def genericFTail (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [word, k, UInt256.ofNat 0xffffffff, e, d, c, b, a, base,
    UInt256.ofNat j, wordIndex, rotation, k, returnDest] ++ rest

set_option linter.unusedSimpArgs false in
theorem run_afterX (q : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 980)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock afterXPath
      { q with pc := UInt256.ofNat 0x13a
               stack := word :: genericTail base j wordIndex rotation k
                 returnDest a b c d e rest } =
      some (BooleanFunctionTrace.fEntry q j b c d (UInt256.ofNat 0x147)
        (genericFTail base j wordIndex rotation k returnDest word a b c d e rest)) := by
  simp (config := { maxSteps := 200000 })
    [afterXPath, roundPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      BooleanFunctionTrace.fEntry, genericTail, genericFTail,
      hrun, hcode, cap rest hstack, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

private def genericT0 (j : Nat) (word k a b c d : UInt256) : UInt256 :=
  UInt256.land (((a + Word.evmF j b c d) + word) + k)
    (UInt256.ofNat 0xffffffff)

private def genericRot1Tail (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [e, UInt256.ofNat 0xffffffff, genericT0 j word k a b c d, e, d, c, b,
    a, base, UInt256.ofNat j, wordIndex, rotation, k, returnDest] ++ rest

set_option linter.unusedSimpArgs false in
theorem run_afterF (q : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 980)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock afterFPath
      (BooleanFunctionTrace.fReturned q j b c d (UInt256.ofNat 0x147)
        (genericFTail base j wordIndex rotation k returnDest word a b c d e rest)) =
      some (rotlEntry q (genericT0 j word k a b c d) rotation
        (UInt256.ofNat 0x15d)
        (genericRot1Tail base j wordIndex rotation k returnDest word
          a b c d e rest)) := by
  simp (config := { maxSteps := 250000 })
    [afterFPath, roundPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      BooleanFunctionTrace.fReturned, genericFTail, genericT0,
      genericRot1Tail, rotlEntry, Challenge.EvmProof.Word.mask32,
      UInt256.instAndOp,
      hrun, hcode, cap rest hstack, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

private def genericNextB (j : Nat) (word rotation k a b c d e : UInt256) :
    UInt256 :=
  UInt256.land (rotlValue (genericT0 j word k a b c d) rotation + e)
    (UInt256.ofNat 0xffffffff)

private def genericAfterFirstStores (q : State) (base e d : UInt256) : State :=
  TableTrace.storedWord
    (TableTrace.storedWord q base (UInt256.ofNat 0) e)
    base (UInt256.ofNat 4) d

private def genericRot2Tail (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat 0x18d, genericNextB j word rotation k a b c d e, e, d,
    c, b, a, base, UInt256.ofNat j, wordIndex, rotation, k, returnDest] ++ rest

set_option linter.unusedSimpArgs false in
theorem run_afterRot1 (q : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 980)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock afterRot1Path
      (rotlReturned q (genericT0 j word k a b c d) rotation
        (UInt256.ofNat 0x15d)
        (genericRot1Tail base j wordIndex rotation k returnDest word
          a b c d e rest)) =
      some (rotlEntry (genericAfterFirstStores q base e d) c (UInt256.ofNat 10)
        (UInt256.ofNat 0x185)
        (genericRot2Tail base j wordIndex rotation k returnDest word
          a b c d e rest)) := by
  simp (config := { maxSteps := 350000 })
    [afterRot1Path, roundPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rotlReturned, rotlValue, genericT0, genericRot1Tail, genericNextB,
      genericAfterFirstStores, genericRot2Tail, rotlEntry,
      TableTrace.storedWord,
      Challenge.EvmProof.Word.mask32, UInt256.instAndOp, UInt256.instOrOp,
      hrun, hcode, cap rest hstack, swap2, Nat.add_assoc,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

private def genericSetTail (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [genericNextB j word rotation k a b c d e, e, d, c, b, a, base,
    UInt256.ofNat j, wordIndex, rotation, k, returnDest] ++ rest

set_option linter.unusedSimpArgs false in
theorem run_afterRot2 (q : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 980)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock afterRot2Path
      (rotlReturned q c (UInt256.ofNat 10) (UInt256.ofNat 0x185)
        (genericRot2Tail base j wordIndex rotation k returnDest word
          a b c d e rest)) =
      some (TableTrace.setEntry q base (UInt256.ofNat 3)
        (rotlValue c (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
        (genericSetTail base j wordIndex rotation k returnDest word
          a b c d e rest)) := by
  simp (config := { maxSteps := 150000 })
    [afterRot2Path, roundPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rotlReturned, genericRot2Tail, TableTrace.setEntry, genericSetTail,
      hrun, hcode, cap rest hstack, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

private def genericAfterThirdStore (q : State) (base c : UInt256) : State :=
  TableTrace.storedWord q base (UInt256.ofNat 3)
    (rotlValue c (UInt256.ofNat 10))

private def genericReturned (q : State) (base : UInt256) (j : Nat)
    (word rotation k returnDest : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) : State :=
  let q' := TableTrace.storedWord (genericAfterThirdStore q base c) base
    (UInt256.ofNat 2) b
  let q'' := TableTrace.storedWord q' base (UInt256.ofNat 1)
    (genericNextB j word rotation k a b c d e)
  { q'' with pc := returnDest, stack := rest }

set_option linter.unusedSimpArgs false in
theorem run_suffix (q : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 980)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hrun : q.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock suffixPath
      (TableTrace.setReturned q base (UInt256.ofNat 3)
        (rotlValue c (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
        (genericSetTail base j wordIndex rotation k returnDest word
          a b c d e rest)) =
      some (genericReturned q base j word rotation k returnDest
        a b c d e rest) := by
  simp (config := { maxSteps := 350000 })
    [suffixPath, roundPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      TableTrace.setReturned, genericSetTail, genericReturned,
      genericAfterThirdStore, genericNextB, TableTrace.storedWord,
      Challenge.EvmProof.Word.mask32,
      UInt256.instAndOp, UInt256.instOrOp,
      hrun, hcode, hvalid, cap rest hstack, Nat.add_assoc,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

private def bodyEntry (q : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) : State :=
  { q with pc := UInt256.ofNat 0x13a
           stack := word :: genericTail base j wordIndex rotation k
             returnDest a b c d e rest }

def gasSteps_roundBody (q : State) (base : UInt256) (j : Nat) (hj : j < 5)
    (wordIndex rotation k returnDest word : UInt256) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 980)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hfork : q.fork = .Osaka) (hrun : q.halt = .Running)
    (hnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (bodyEntry q base j wordIndex rotation k returnDest word a b c d e rest)
      (genericReturned (genericAfterFirstStores q base e d) base j
        word rotation k returnDest a b c d e rest) := by
  have gAfterX := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka afterXPath
      (s := bodyEntry q base j wordIndex rotation k returnDest word a b c d e rest)
      hcode hfork
      (run_afterX q base j wordIndex rotation k returnDest word a b c d e rest
        hstack hcode hrun) hrun hnp
  have gF := BooleanFunctionTrace.gasSteps_fCase q j hj b c d
    (UInt256.ofNat 0x147)
    (genericFTail base j wordIndex rotation k returnDest word a b c d e rest)
    (by simp [genericFTail]; omega) hcode hfork hrun hnp valid147
  have gAfterF := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka afterFPath
      (s := BooleanFunctionTrace.fReturned q j b c d (UInt256.ofNat 0x147)
        (genericFTail base j wordIndex rotation k returnDest word a b c d e rest))
      hcode hfork
      (run_afterF q base j wordIndex rotation k returnDest word a b c d e rest
        hstack hcode hrun) hrun hnp
  have gRot1 := gasSteps_rotl q (genericT0 j word k a b c d) rotation
    (UInt256.ofNat 0x15d)
    (genericRot1Tail base j wordIndex rotation k returnDest word a b c d e rest)
    (by simp [genericRot1Tail]; omega) hcode hfork hrun hnp valid15D
  let q2 := genericAfterFirstStores q base e d
  have hcode2 : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hcode
  have hfork2 : q2.fork = .Osaka := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hfork
  have hrun2 : q2.halt = .Running := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hrun
  have hnp2 : Precompile.isPrecompile q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hnp
  have gAfterRot1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka afterRot1Path
      (s := rotlReturned q (genericT0 j word k a b c d) rotation
        (UInt256.ofNat 0x15d)
        (genericRot1Tail base j wordIndex rotation k returnDest word
          a b c d e rest))
      hcode hfork
      (run_afterRot1 q base j wordIndex rotation k returnDest word a b c d e rest
        hstack hcode hrun) hrun hnp
  have gRot2 := gasSteps_rotl q2 c (UInt256.ofNat 10) (UInt256.ofNat 0x185)
    (genericRot2Tail base j wordIndex rotation k returnDest word a b c d e rest)
    (by simp [genericRot2Tail]; omega) hcode2 hfork2 hrun2 hnp2 valid185
  have gAfterRot2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka afterRot2Path
      (s := rotlReturned q2 c (UInt256.ofNat 10) (UInt256.ofNat 0x185)
        (genericRot2Tail base j wordIndex rotation k returnDest word
          a b c d e rest))
      hcode2 hfork2
      (run_afterRot2 q2 base j wordIndex rotation k returnDest word a b c d e rest
        hstack hcode2 hrun2) hrun2 hnp2
  have gSet := TableTrace.gasSteps_wordSet q2 base (UInt256.ofNat 3)
    (rotlValue c (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
    (genericSetTail base j wordIndex rotation k returnDest word a b c d e rest)
    (by simp [genericSetTail]; omega) hcode2 hfork2 hrun2 hnp2 valid18D
  have gSuffix := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka suffixPath
      (s := TableTrace.setReturned q2 base (UInt256.ofNat 3)
        (rotlValue c (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
        (genericSetTail base j wordIndex rotation k returnDest word
          a b c d e rest))
      hcode2 hfork2
      (run_suffix q2 base j wordIndex rotation k returnDest word a b c d e rest
        hstack hcode2 hrun2 hvalid) hrun2 hnp2
  exact gAfterX.trans (gF.trans (gAfterF.trans (gRot1.trans
    (gAfterRot1.trans (gRot2.trans (gAfterRot2.trans (gSet.trans gSuffix)))))))

def roundWord (s : State) (base wordIndex : UInt256) : UInt256 :=
  TableTrace.loadedWord (afterLoads s base)
    (UInt256.ofNat 0x2a0) wordIndex

def roundReturned (s : State) (base : UInt256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256) : State :=
  let q := xReturnedState s base j wordIndex rotation k returnDest rest
  genericReturned (genericAfterFirstStores q base (loadedE s base) (loadedD s base))
    base j (roundWord s base wordIndex) rotation k returnDest
    (loadedA s base) (loadedB s base) (loadedC s base) (loadedD s base)
    (loadedE s base) rest

def gasSteps_round (s : State) (base : UInt256) (j : Nat) (hj : j < 5)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 980)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (roundEntry s base j wordIndex rotation k returnDest rest)
      (roundReturned s base j wordIndex rotation k returnDest rest) := by
  have gPrefix := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka prefixPath
      (s := roundEntry s base j wordIndex rotation k returnDest rest)
      hcode hfork
      (run_prefix s base j wordIndex rotation k returnDest rest
        hstack hcode hrun)
      hrun hnp
  let q0 := afterLoads s base
  have hcode0 : q0.executionEnv.code = referenceBytecode := by
    simpa [q0, afterLoads] using hcode
  have hfork0 : q0.fork = .Osaka := by simpa [q0, afterLoads] using hfork
  have hrun0 : q0.halt = .Running := by simpa [q0, afterLoads] using hrun
  have hnp0 : Precompile.isPrecompile q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by simpa [q0, afterLoads] using hnp
  have gX := TableTrace.gasSteps_xAt q0 wordIndex (UInt256.ofNat 0x13a)
    (roundTail s base j wordIndex rotation k returnDest rest)
    (by simp [roundTail]; omega) hcode0 hfork0 hrun0 hnp0 valid13A
  let q := xReturnedState s base j wordIndex rotation k returnDest rest
  have hcodeQ : q.executionEnv.code = referenceBytecode := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hcode
  have hforkQ : q.fork = .Osaka := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hfork
  have hrunQ : q.halt = .Running := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hrun
  have hnpQ : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hnp
  have gBody := gasSteps_roundBody q base j hj wordIndex rotation k returnDest
    (roundWord s base wordIndex) (loadedA s base) (loadedB s base) (loadedC s base)
    (loadedD s base) (loadedE s base) rest hstack hcodeQ hforkQ hrunQ hnpQ hvalid
  have hxStart : xCallState s base j wordIndex rotation k returnDest rest =
      TableTrace.atEntry q0 (UInt256.ofNat 0x4b) wordIndex
        (UInt256.ofNat 0x13a)
        (roundTail s base j wordIndex rotation k returnDest rest) := by
    rfl
  have hxEnd : TableTrace.atReturned q0 (UInt256.ofNat 0x2a0) wordIndex
      (UInt256.ofNat 0x13a)
      (roundTail s base j wordIndex rotation k returnDest rest) =
      bodyEntry q base j wordIndex rotation k returnDest
        (roundWord s base wordIndex) (loadedA s base) (loadedB s base)
        (loadedC s base) (loadedD s base) (loadedE s base) rest := by
    simp [q, q0, xReturnedState, bodyEntry, roundWord, genericTail, roundTail,
      TableTrace.atReturned, TableTrace.loadedWord]
  have gX' := Challenge.EvmProof.GasSteps.cast gX hxStart.symm hxEnd
  exact gPrefix.trans (gX'.trans gBody)

/-! ## Functional bridge -/

/-- Register values written by the compiled helper, including the masks at
each store boundary. -/
def roundResult (x : Compression.EvmWorking) (j : Nat) (word : UInt256)
    (rotation : Nat) (k : UInt256) : Compression.EvmWorking :=
  { a := UInt256.land x.e (UInt256.ofNat 0xffffffff)
    b := genericNextB j word (UInt256.ofNat rotation) k
      x.a x.b x.c x.d x.e
    c := UInt256.land x.b (UInt256.ofNat 0xffffffff)
    d := UInt256.land (rotlValue x.c (UInt256.ofNat 10))
      (UInt256.ofNat 0xffffffff)
    e := UInt256.land x.d (UInt256.ofNat 0xffffffff) }

/-- The five contiguous words at a non-wrapping natural-number base. -/
def workingAtNat (s : State) (base : Nat) : Compression.EvmWorking :=
  { a := MachineState.readWord s.memory base
    b := MachineState.readWord s.memory (base + 32)
    c := MachineState.readWord s.memory (base + 64)
    d := MachineState.readWord s.memory (base + 96)
    e := MachineState.readWord s.memory (base + 128) }

private theorem readWord_writePadded32_disjoint (memory : ByteArray)
    (value readStart writeStart : Nat)
    (hdisjoint : readStart + 32 ≤ writeStart ∨
      writeStart + 32 ≤ readStart) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) writeStart) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

private theorem land_mask32_idem (x : UInt256) :
    UInt256.land
        (UInt256.land x (UInt256.ofNat 0xffffffff))
        (UInt256.ofNat 0xffffffff) =
      UInt256.land x (UInt256.ofNat 0xffffffff) := by
  change (x &&& UInt256.ofNat 0xffffffff) &&&
      UInt256.ofNat 0xffffffff = x &&& UInt256.ofNat 0xffffffff
  simpa [Challenge.EvmProof.Word.mask32] using
    Challenge.EvmProof.Word.mask32_idem x

set_option linter.unusedSimpArgs false in
/-- The concrete helper's five stores are exactly `roundResult`. -/
theorem roundReturned_workingAtNat (s : State) (base : Nat)
    (hbase : base + 160 < 2 ^ 256) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (rest : List UInt256) :
    workingAtNat
        (roundReturned s (UInt256.ofNat base) j wordIndex rotation k
          returnDest rest) base =
      roundResult (workingAtNat s base) j
        (roundWord s (UInt256.ofNat base) wordIndex) rotation.toNat k := by
  have hslot (n : Nat) (hn : n ≤ 4) :
      TableTrace.slotAddress (UInt256.ofNat base) (UInt256.ofNat n) =
        UInt256.ofNat (base + n * 32) := by
    exact TableTrace.slotAddress_ofNat base n (by omega) (by omega)
  have htoNat (n : Nat) (hn : n ≤ 160) :
      (UInt256.ofNat (base + n)).toNat = base + n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hbaseToNat : (UInt256.ofNat base).toNat = base := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hadd (n : Nat) (hn : n ≤ 160) :
      UInt256.ofNat base + UInt256.ofNat n = UInt256.ofNat (base + n) := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hrotation : UInt256.ofNat rotation.toNat = rotation := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt rotation.val.isLt
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [workingAtNat, roundReturned, genericReturned, genericAfterThirdStore,
      genericAfterFirstStores, genericNextB, genericT0, xReturnedState,
      afterLoads, roundResult, roundWord, loadedA, loadedB, loadedC, loadedD,
      loadedE, TableTrace.atReturned, TableTrace.storedWord,
      hslot, hadd, htoNat, hbaseToNat, hrotation,
      Challenge.EvmProof.Memory.readWord_writeWord,
      readWord_writePadded32_disjoint,
      Challenge.EvmProof.Word.mask32,
      Challenge.EvmProof.Word.mask32_idem, land_mask32_idem]

set_option linter.unusedSimpArgs false in
/-- All 32-byte words disjoint from the five-word working region survive a
round unchanged. -/
theorem roundReturned_word_outside (s : State) (base address : Nat)
    (hbase : base + 160 < 2 ^ 256)
    (houtside : address + 32 ≤ base ∨ base + 160 ≤ address)
    (j : Nat) (wordIndex rotation k returnDest : UInt256)
    (rest : List UInt256) :
    MachineState.readWord
        (roundReturned s (UInt256.ofNat base) j wordIndex rotation k
          returnDest rest).memory address =
      MachineState.readWord s.memory address := by
  have hslot (n : Nat) (hn : n ≤ 4) :
      TableTrace.slotAddress (UInt256.ofNat base) (UInt256.ofNat n) =
        UInt256.ofNat (base + n * 32) := by
    exact TableTrace.slotAddress_ofNat base n (by omega) (by omega)
  have htoNat (n : Nat) (hn : n ≤ 160) :
      (UInt256.ofNat (base + n)).toNat = base + n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hbaseToNat : (UInt256.ofNat base).toNat = base := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hadd (n : Nat) (hn : n ≤ 160) :
      UInt256.ofNat base + UInt256.ofNat n = UInt256.ofNat (base + n) := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  rcases houtside with hbefore | hafter
  all_goals
    simp (config := { maxSteps := 500000 }) (discharger := omega)
      [roundReturned, genericReturned, genericAfterThirdStore,
        genericAfterFirstStores, xReturnedState, afterLoads,
        TableTrace.atReturned, TableTrace.storedWord,
        hslot, hadd, htoNat, hbaseToNat,
        readWord_writePadded32_disjoint]

private theorem rotlValue_ofUInt32 (x : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    rotlValue (Challenge.EvmProof.Word.ofUInt32 x) (UInt256.ofNat n) =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.rotl32 x n) := by
  unfold rotlValue
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := 32) (b := n) (by omega) (by norm_num)]
  exact Challenge.EvmProof.Word.evm_rotl32 x n hn0 hn

private theorem landMask_eq (v : UInt256) :
    UInt256.land v (UInt256.ofNat 0xffffffff) =
      Challenge.EvmProof.Word.mask32 v := by rfl

set_option linter.unusedSimpArgs false in
theorem roundResult_embed (x : Compression.Working) (j : Nat)
    (word constant : UInt32) (rotation : Nat) (hj : j < 5)
    (hr0 : 0 < rotation) (hr : rotation < 32) :
    roundResult (Compression.embed x) j
      (Challenge.EvmProof.Word.ofUInt32 word) rotation
      (Challenge.EvmProof.Word.ofUInt32 constant) =
      Compression.embed (Compression.round x j word rotation constant) := by
  unfold roundResult genericNextB genericT0 Compression.embed Compression.round
  simp [landMask_eq, Word.evmF_ofUInt32 j x.b x.c x.d hj,
    Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.toUInt32_add,
    Challenge.EvmProof.Word.toUInt32_ofUInt32,
    rotlValue_ofUInt32 _ rotation hr0 hr,
    rotlValue_ofUInt32 x.c 10 (by decide) (by decide)]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.RoundTrace
