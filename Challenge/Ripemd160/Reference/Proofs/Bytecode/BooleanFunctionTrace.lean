import Challenge.Ripemd160.Reference.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Word
import YulEvmCompiler.LowerDefs
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Direct trace of the RIPEMD-160 Boolean helper

The compiler represents `f(j,x,y,z)` by the frame
`[j,x,y,z,0,returnDest]`.  These five paths certify the four switch tests,
the five Boolean arms, the shared cleanup block, and the final return jump.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.BooleanFunctionTrace

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

private def helperPCs : List Nat :=
  [147, 148, 149, 150, 151, 152, 153, 156, 157, 158, 159, 160, 161, 162,
   163, 164, 165, 168, 169, 170, 171, 173, 174, 175, 178, 179, 180, 181,
   182, 183, 184, 185, 186, 187, 188, 189, 190, 193, 194, 195, 196, 198,
   199, 200, 203, 204, 205, 210, 211, 212, 213, 214, 215, 216, 217, 218,
   219, 222, 223, 224, 225, 227, 228, 229, 232, 233, 234, 235, 236, 237,
   238, 239, 240, 241, 242, 243, 244, 247, 248, 249, 250, 255, 256, 257,
   258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270]

@[simp] private theorem helperPC (i : Nat) (hlo : 108 ≤ i) (hhi : i ≤ 204) :
    Artifact.instructionPC i = helperPCs[i - 108]! := by
  interval_cases i <;> rfl

@[simp] private theorem helperRefPC (i : Nat) (hlo : 108 ≤ i) (hhi : i ≤ 204) :
    Artifact.referenceArtifact.instructionPC i = helperPCs[i - 108]! := by
  interval_cases i <;> rfl

@[simp] private theorem helperAdd (a b : Nat) (ha : a ≤ 270) (hb : b ≤ 5) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)

@[simp] private theorem helperSucc (a : Nat) (ha : a ≤ 270) :
    (UInt256.ofNat a).succ = UInt256.ofNat (a + 1) := by
  exact Challenge.EvmProof.Word.succ_ofNat (by omega)

@[simp] private theorem helperToNat (a : Nat) (ha : a ≤ 270) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[simp] private theorem numeralToNat (a : Nat) :
    UInt256.toNat (OfNat.ofNat a : UInt256) = a % 2 ^ 256 := by
  exact Challenge.EvmProof.Word.word_toNat_ofNat a

@[simp] private theorem numeralSucc (a : Nat) (ha : a ≤ 269) :
    (OfNat.ofNat a : UInt256).succ = UInt256.ofNat (a + 1) := by
  exact helperSucc a (by omega)

@[simp] private theorem numeralAdd (a b : Nat) (ha : a ≤ 270) (hb : b ≤ 5) :
    (OfNat.ofNat a : UInt256) + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  exact helperAdd a b ha hb

@[simp] private theorem mkToNat (a : Fin UInt256.size) :
    UInt256.toNat ⟨a⟩ = a.val := rfl

@[simp] private theorem helperEq (a b : Nat) (ha : a ≤ 4) (hb : b ≤ 4) :
    (UInt256.ofNat a).eq (UInt256.ofNat b) =
      UInt256.ofNat (if a = b then 1 else 0) := by
  interval_cases a <;> interval_cases b <;> decide

@[simp] private theorem helperIsZero0 :
    (UInt256.ofNat 0).isZero = UInt256.ofNat 1 := by decide

@[simp] private theorem helperIsZero1 :
    (UInt256.ofNat 1).isZero = UInt256.ofNat 0 := by decide

def test0 : List Located :=
  [⟨108, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨109, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨110, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨111, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨112, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨113, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨114, .push ⟨2, by decide⟩ (UInt256.ofNat 0xa9), by rfl, by decide⟩,
   ⟨115, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def arm0 : List Located :=
  [⟨116, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨117, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨118, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨119, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨120, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨121, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨122, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨123, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨124, .push ⟨2, by decide⟩ (UInt256.ofNat 0x108), by rfl, by decide⟩,
   ⟨125, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def test1 : List Located :=
  [⟨126, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨127, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨128, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨129, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨130, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨131, .push ⟨2, by decide⟩ (UInt256.ofNat 0xc2), by rfl, by decide⟩,
   ⟨132, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def arm1 : List Located :=
  [⟨133, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨134, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨135, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨136, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨137, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨138, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨139, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨140, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨141, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨142, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨143, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨144, .push ⟨2, by decide⟩ (UInt256.ofNat 0x108), by rfl, by decide⟩,
   ⟨145, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def test2 : List Located :=
  [⟨146, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨147, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨148, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨149, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨150, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨151, .push ⟨2, by decide⟩ (UInt256.ofNat 0xdf), by rfl, by decide⟩,
   ⟨152, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def arm2 : List Located :=
  [⟨153, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨154, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨155, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨156, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨157, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨158, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨159, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨160, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨161, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨162, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨163, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨164, .push ⟨2, by decide⟩ (UInt256.ofNat 0x108), by rfl, by decide⟩,
   ⟨165, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def test3 : List Located :=
  [⟨166, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨167, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨168, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨169, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨170, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨171, .push ⟨2, by decide⟩ (UInt256.ofNat 0xf8), by rfl, by decide⟩,
   ⟨172, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def arm3 : List Located :=
  [⟨173, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨174, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨175, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨176, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨177, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨178, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨180, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨181, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨182, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨183, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨184, .push ⟨2, by decide⟩ (UInt256.ofNat 0x108), by rfl, by decide⟩,
   ⟨185, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def arm4 : List Located :=
  [⟨186, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨187, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨188, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨189, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨190, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨191, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨192, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨193, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨194, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨195, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨196, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨197, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def cleanup : List Located :=
  [⟨198, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨199, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨200, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨201, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨202, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨203, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨204, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def casePath : Nat → List Located
  | 0 => test0 ++ arm0 ++ cleanup
  | 1 => test0 ++ test1 ++ arm1 ++ cleanup
  | 2 => test0 ++ test1 ++ test2 ++ arm2 ++ cleanup
  | 3 => test0 ++ test1 ++ test2 ++ test3 ++ arm3 ++ cleanup
  | _ => test0 ++ test1 ++ test2 ++ test3 ++ arm4 ++ cleanup

def fEntry (s : State) (j : Nat) (x y z returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0x93
    stack := [UInt256.ofNat j, x, y, z, 0, returnDest] ++ rest }

def fReturned (s : State) (j : Nat) (x y z returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := Word.evmF j x y z :: rest }

@[simp] private theorem validA9 :
    Decode.isValidJumpDest referenceBytecode 0xa9 = true := by
  have hpc : Artifact.referenceArtifact.instructionPC 126 = 0xa9 := by rfl
  rw [← hpc]
  exact Artifact.referenceArtifact.isValidJumpDest_index 126 (by rfl)

@[simp] private theorem validC2 :
    Decode.isValidJumpDest referenceBytecode 0xc2 = true := by
  have hpc : Artifact.referenceArtifact.instructionPC 146 = 0xc2 := by rfl
  rw [← hpc]
  exact Artifact.referenceArtifact.isValidJumpDest_index 146 (by rfl)

@[simp] private theorem validDF :
    Decode.isValidJumpDest referenceBytecode 0xdf = true := by
  have hpc : Artifact.referenceArtifact.instructionPC 166 = 0xdf := by rfl
  rw [← hpc]
  exact Artifact.referenceArtifact.isValidJumpDest_index 166 (by rfl)

@[simp] private theorem validF8 :
    Decode.isValidJumpDest referenceBytecode 0xf8 = true := by
  have hpc : Artifact.referenceArtifact.instructionPC 186 = 0xf8 := by rfl
  rw [← hpc]
  exact Artifact.referenceArtifact.isValidJumpDest_index 186 (by rfl)

@[simp] private theorem valid108 :
    Decode.isValidJumpDest referenceBytecode 0x108 = true := by
  have hpc : Artifact.referenceArtifact.instructionPC 198 = 0x108 := by rfl
  rw [← hpc]
  exact Artifact.referenceArtifact.isValidJumpDest_index 198 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_fCase (s : State) (j : Nat) (hj : j < 5)
    (x y z returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1008) (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock (casePath j)
      (fEntry s j x y z returnDest rest) =
        some (fReturned s j x y z returnDest rest) := by
  have hcap (n : Nat) (hn : n ≤ 15) : rest.length + n < 1024 := by omega
  have hswap6 (a b c d e f : UInt256) (rho : List UInt256) :
      (a :: b :: c :: d :: e :: f :: rho).exchange 0 5 =
        some (f :: b :: c :: d :: e :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a f [b, c, d, e] rho
  have hswap2 (a b : UInt256) (rho : List UInt256) :
      (a :: b :: rho).exchange 0 1 = some (b :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a b ([] : List UInt256) rho
  interval_cases j <;>
    simp (config := { maxSteps := 500000 })
      [casePath, test0, arm0, test1, arm1, test2, arm2, test3, arm3,
        arm4, cleanup, helperPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
        fEntry, fReturned, Word.evmF, Challenge.EvmProof.Word.mask32,
        hrun, hcode, hvalid, hcap, hswap6, hswap2, Nat.add_assoc,
        UInt256.eq, UInt256.isZero, UInt256.isTrue,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat] <;> rfl

def gasSteps_fCase (s : State) (j : Nat) (hj : j < 5)
    (x y z returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1008) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (fEntry s j x y z returnDest rest)
      (fReturned s j x y z returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka (casePath j)
  · exact hcode
  · exact hfork
  · exact run_fCase s j hj x y z returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

theorem fReturned_ofUInt32 (s : State) (j : Nat) (hj : j < 5)
    (x y z : UInt32) (returnDest : UInt256) (rest : List UInt256) :
    (fReturned s j (Challenge.EvmProof.Word.ofUInt32 x)
      (Challenge.EvmProof.Word.ofUInt32 y) (Challenge.EvmProof.Word.ofUInt32 z)
      returnDest rest).stack =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.f j x y z) :: rest := by
  simp [fReturned, Word.evmF_ofUInt32 j x y z hj]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.BooleanFunctionTrace
