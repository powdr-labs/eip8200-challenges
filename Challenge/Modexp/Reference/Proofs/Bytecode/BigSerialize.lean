import Challenge.Modexp.Reference.Proofs.Bytecode.BigExponentGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Certified multi-limb result serialization and return -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigSerialize

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open BigExponent

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def outerFinishGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 719 .JUMPDEST, opAt 720 (.Dup ⟨4, by decide⟩),
   opAt 721 (.Dup ⟨1, by decide⟩), opAt 722 .LT, opAt 723 .ISZERO,
   pushAt 724 2 1118, opAt 725 .JUMPI]

def serializerEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 838 .JUMPDEST, opAt 839 .POP, pushAt 840 0 0]

def serializerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 841 .JUMPDEST, opAt 842 (.Dup ⟨5, by decide⟩),
   opAt 843 (.Dup ⟨1, by decide⟩), opAt 844 .LT, opAt 845 .ISZERO,
   pushAt 846 2 1180, opAt 847 .JUMPI]

def serializerBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 848 (.Dup ⟨0, by decide⟩), pushAt 849 1 1,
   opAt 850 (.Dup ⟨7, by decide⟩), opAt 851 .SUB, opAt 852 .SUB,
   opAt 853 (.Dup ⟨0, by decide⟩), pushAt 854 1 5, opAt 855 .SHR,
   pushAt 856 1 31, opAt 857 (.Dup ⟨2, by decide⟩), opAt 858 .AND,
   pushAt 859 1 3, opAt 860 .SHL, pushAt 861 1 255,
   opAt 862 (.Dup ⟨2, by decide⟩), pushAt 863 1 5, opAt 864 .SHL,
   pushAt 865 2 2048, opAt 866 .ADD, opAt 867 .MLOAD,
   opAt 868 (.Dup ⟨2, by decide⟩), opAt 869 .SHR, opAt 870 .AND,
   opAt 871 (.Dup ⟨4, by decide⟩), pushAt 872 2 6144,
   opAt 873 .ADD, opAt 874 .MSTORE8, opAt 875 .POP, opAt 876 .POP,
   opAt 877 .POP, pushAt 878 1 1, opAt 879 (.Dup ⟨1, by decide⟩),
   opAt 880 .ADD, opAt 881 (.Swap ⟨0, by decide⟩), opAt 882 .POP,
   pushAt 883 2 1121, opAt 884 .JUMP]

def serializerReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 885 .JUMPDEST, opAt 886 .POP, opAt 887 (.Dup ⟨4, by decide⟩),
   pushAt 888 2 6144, opAt 889 .RETURN]

def exponentOuterExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest e with
    pc := UInt256.ofNat 1118 }

def serializerEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1118
           stack := [UInt256.ofNat e, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def reverseIndex (m k : Nat) : UInt256 :=
  (UInt256.ofNat m - UInt256.ofNat 1) - UInt256.ofNat k

def serializerLimb (m k : Nat) : UInt256 :=
  UInt256.shiftRight (reverseIndex m k) (UInt256.ofNat 5)

def serializerShift (m k : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.land (reverseIndex m k) (UInt256.ofNat 31))
    (UInt256.ofNat 3)

def serializedByte (memory : ByteArray) (m k : Nat) : UInt256 :=
  let word := MachineState.readWord memory
    (2048 + UInt256.shiftLeft (serializerLimb m k) (UInt256.ofNat 5)).toNat
  UInt256.land (UInt256.shiftRight word (serializerShift m k))
    (UInt256.ofNat 255)

def serializeMemory (memory : ByteArray) (m : Nat) : Nat → ByteArray
  | 0 => memory
  | k + 1 =>
      let before := serializeMemory memory m k
      MachineState.writeBytes before
        (ByteArray.mk #[UInt8.ofNat ((serializedByte before m k).toNat % 256)])
        (6144 + UInt256.ofNat k).toNat

def serializeWords (active : UInt256) (m : Nat) : Nat → UInt256
  | 0 => active
  | k + 1 =>
      let before := serializeWords active m k
      let loaded := UInt256.ofNat (MachineState.activeWordsAfter before.toNat
        (2048 + UInt256.shiftLeft (serializerLimb m k) (UInt256.ofNat 5)).toNat 32)
      UInt256.ofNat (MachineState.activeWordsAfter loaded.toNat
        (6144 + UInt256.ofNat k).toNat 1)

def serializeProgress (s : State) (m : Nat) (k : Nat) : State :=
  { s with memory := serializeMemory s.memory m k
           activeWords := serializeWords s.activeWords m k }

@[simp] theorem serializeProgress_halt (s : State) (m k : Nat) :
    (serializeProgress s m k).halt = s.halt := by
  rfl

@[simp] theorem serializeProgress_executionEnv (s : State) (m k : Nat) :
    (serializeProgress s m k).executionEnv = s.executionEnv := by
  rfl

def serializerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (k : Nat) : State :=
  { serializeProgress s m k with
    pc := UInt256.ofNat 1121
    stack := [UInt256.ofNat k, accumulatorWord, UInt256.ofNat count,
      UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def serializerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (k : Nat) : State :=
  { serializerLoop s accumulatorWord count b e m baseOff expOff rest k with
    pc := UInt256.ofNat 1130 }

def serializerExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { serializerLoop s accumulatorWord count b e m baseOff expOff rest m with
    pc := UInt256.ofNat 1180 }

def bigReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  let current := serializeProgress s m m
  { current with
    pc := UInt256.ofNat 1186
    stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
      UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
      UInt256.ofNat expOff] ++ rest
    halt := .Returned
    hReturn := MachineState.readPadded current.memory 6144 m
    activeWords := UInt256.ofNat
      (MachineState.activeWordsAfter current.activeWords.toNat 6144 m) }

@[simp] private theorem outerFinishPCs (i : Nat) (hi : 719 ≤ i)
    (hii : i ≤ 725) :
    Artifact.referenceArtifact.instructionPC i =
      ([946,947,948,949,950,951,954])[i - 719]! := by
  interval_cases i <;> decide

@[simp] private theorem serializerPCs (i : Nat) (hi : 838 ≤ i)
    (hii : i ≤ 889) :
    Artifact.referenceArtifact.instructionPC i =
      ([1118,1119,1120,1121,1122,1123,1124,1125,1126,1129,1130,1131,
        1133,1134,1135,1136,1137,1139,1140,1142,1143,1144,1146,1147,
        1149,1150,1152,1153,1156,1157,1158,1159,1160,1161,1162,1165,
        1166,1167,1168,1169,1170,1172,1173,1174,1175,1176,1179,1180,
        1181,1182,1183,1186])[i - 838]! := by
  interval_cases i <;> decide

private theorem jump1118 :
    Decode.isValidJumpDest referenceBytecode 1118 = true :=
  Artifact.isValidJumpDest_index 838 (by rfl)

private theorem jump1121 :
    Decode.isValidJumpDest referenceBytecode 1121 = true :=
  Artifact.isValidJumpDest_index 841 (by rfl)

private theorem jump1180 :
    Decode.isValidJumpDest referenceBytecode 1180 = true :=
  Artifact.isValidJumpDest_index 885 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_outerFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (_he : e < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerFinishGuardPath
      (outerLoop s accumulatorWord count b e m baseOff expOff rest e) =
      some (exponentOuterExit s accumulatorWord count b e m baseOff expOff
        rest) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h1118 : (1118 : UInt256).toNat = 1118 := by decide
  have h1118Word : (1118 : UInt256) = UInt256.ofNat 1118 := by decide
  simp [outerFinishGuardPath, opAt, pushAt, wfOp, outerLoop,
    exponentOuterExit, outerFinishPCs,
    hcode, hrun, hzeroFalse, h1118, h1118Word, jump1118,
    hc8, hc9, hc10, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerEntryPath
      (serializerEntry s accumulatorWord count b e m baseOff expOff rest) =
      some (serializerLoop s accumulatorWord count b e m baseOff expOff rest
        0) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [serializerEntryPath, opAt, pushAt, wfOp, serializerEntry,
    serializerLoop, serializeProgress, serializeMemory, serializeWords,
    serializerPCs, hrun, hzero, hc7, hc8,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff k : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (hm : m < 2 ^ 256) (hk : k < m)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerGuardPath
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest k) =
      some (serializerBody s accumulatorWord count b e m baseOff expOff rest
        k) := by
  have hk256 : k < 2 ^ 256 := hk.trans hm
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat k) (UInt256.ofNat m) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hk256, Nat.mod_eq_of_lt hm, if_pos hk]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [serializerGuardPath, opAt, pushAt, wfOp, serializerLoop,
    serializerBody, serializerPCs, hrun, hlt, honeNat, hc8, hc9, hc10,
    UInt256.isTrue, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff k : Nat) (rest : List UInt256)
    (hcap : rest.length < 1008) (hm : m < 2 ^ 256) (hk : k < m)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerBodyPath
      (serializerBody s accumulatorWord count b e m baseOff expOff rest k) =
      some (serializerLoop s accumulatorWord count b e m baseOff expOff rest
        (k + 1)) := by
  have hk256 : k + 1 < 2 ^ 256 := by omega
  have hkm : k + 1 ≤ m := by omega
  have hmPos : 1 ≤ m := by omega
  have hsubM := Challenge.EvmProof.Word.ofNat_sub_ofNat hmPos
    (by exact hm)
  have hsubK := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : k ≤ m - 1)
    (by omega : m - 1 < 2 ^ 256)
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := k) (b := 1) hk256
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h1121 : (1121 : UInt256).toNat = 1121 := by decide
  have h1121Word : (1121 : UInt256) = UInt256.ofNat 1121 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hthree : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h31 : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  simp (config := { maxSteps := 400000 })
    [serializerBodyPath, opAt, pushAt, wfOp, serializerBody, serializerLoop,
      serializeProgress, serializeMemory, serializeWords, serializedByte,
      serializerLimb, serializerShift, reverseIndex, serializerPCs,
      hcode, hrun, hm, hk, hkm, hsubM, hsubK, hinc, jump1121,
      h1121, h1121Word, hone, hthree, hfive, h31, h255,
      hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (_hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerGuardPath
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest m) =
      some (serializerExit s accumulatorWord count b e m baseOff expOff
        rest) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h1180 : (1180 : UInt256).toNat = 1180 := by decide
  have h1180Word : (1180 : UInt256) = UInt256.ofNat 1180 := by decide
  simp [serializerGuardPath, opAt, pushAt, wfOp, serializerLoop,
    serializerExit, serializerPCs, hcode, hrun, hzeroFalse,
    h1180, h1180Word, jump1180, hc8, hc9, hc10,
    UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerReturn (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (hm : m < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerReturnPath
      (serializerExit s accumulatorWord count b e m baseOff expOff rest) =
      some (bigReturned s accumulatorWord count b e m baseOff expOff rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h6144 : (6144 : UInt256).toNat = 6144 := by decide
  have hmNat : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hm]
  simp [serializerReturnPath, opAt, pushAt, wfOp, serializerExit,
    serializerLoop, bigReturned, serializerPCs, hrun, h6144, hmNat,
    hc7, hc8, hc9, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def gasSteps_serializerIteration (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff k : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hm : m < 2 ^ 256) (hk : k < m)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest k)
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest
        (k + 1)) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka serializerGuardPath
      (by simpa [serializerLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [serializerLoop, State.fork] using hfork)
      (run_serializerGuard s accumulatorWord count b e m baseOff expOff k rest
        (by omega) hm hk hrun)
      (by simpa [serializerLoop] using hrun)
      (by simpa [serializerLoop, State.fork] using hnp)
  have hbody := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka serializerBodyPath
      (by simpa [serializerBody, serializerLoop,
        Artifact.referenceArtifact] using hcode)
      (by simpa [serializerBody, serializerLoop, State.fork] using hfork)
      (run_serializerBody s accumulatorWord count b e m baseOff expOff k rest
        (by omega) hm hk hcode hrun)
      (by simpa [serializerBody, serializerLoop] using hrun)
      (by simpa [serializerBody, serializerLoop, State.fork] using hnp)
  exact hguard.trans hbody

theorem gasSteps_serializerIteration_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff k : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hm : m < 2 ^ 256) (hk : k < m)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializerIteration s accumulatorWord count b e m baseOff expOff
      k rest hcap hm hk hcode hfork hrun hnp).cost +
        MachineState.memCost
          (serializerLoop s accumulatorWord count b e m baseOff expOff rest
            k).activeWords.toNat =
      138 + MachineState.memCost
        (serializerLoop s accumulatorWord count b e m baseOff expOff rest
          (k + 1)).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerGuardPath 26
        (run_serializerGuard s accumulatorWord count b e m baseOff expOff k
          rest (by omega) hm hk hrun)
        (by simpa [serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hbody :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerBodyPath 112
        (run_serializerBody s accumulatorWord count b e m baseOff expOff k
          rest (by omega) hm hk hcode hrun)
        (by simpa [serializerBody, serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  unfold gasSteps_serializerIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [serializerLoop, serializerBody] at hguard hbody ⊢
  omega

def gasSteps_serializerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest 0)
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest m) :=
  Challenge.EvmProof.GasSteps.iterateBounded m fun k hk =>
    gasSteps_serializerIteration s accumulatorWord count b e m baseOff expOff k
      rest hcap hm hk hcode hfork hrun hnp

theorem gasSteps_serializerLoop_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hm : m < 2 ^ 256) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializerLoop s accumulatorWord count b e m baseOff expOff rest
      hcap hm hcode hfork hrun hnp).cost +
        MachineState.memCost
          (serializerLoop s accumulatorWord count b e m baseOff expOff rest
            0).activeWords.toNat =
      m * 138 + MachineState.memCost
        (serializerLoop s accumulatorWord count b e m baseOff expOff rest
          m).activeWords.toNat := by
  unfold gasSteps_serializerLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro k hk
  simpa [Nat.mul_comm] using
    gasSteps_serializerIteration_cost_potential s accumulatorWord count b e m
      baseOff expOff k rest hcap hm hk hcode hfork hrun hnp

def gasSteps_serializerFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest m)
      (bigReturned s accumulatorWord count b e m baseOff expOff rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka serializerGuardPath
      (by simpa [serializerLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [serializerLoop, State.fork] using hfork)
      (run_serializerFinishGuard s accumulatorWord count b e m baseOff expOff
        rest (by omega) hm hcode hrun)
      (by simpa [serializerLoop] using hrun)
      (by simpa [serializerLoop, State.fork] using hnp)
  have hreturn := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka serializerReturnPath
      (by simpa [serializerExit, serializerLoop,
        Artifact.referenceArtifact] using hcode)
      (by simpa [serializerExit, serializerLoop, State.fork] using hfork)
      (run_serializerReturn s accumulatorWord count b e m baseOff expOff rest
        (by omega) hm hrun)
      (by simpa [serializerExit, serializerLoop] using hrun)
      (by simpa [serializerExit, serializerLoop, State.fork] using hnp)
  exact hguard.trans hreturn

theorem gasSteps_serializerFinish_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hm : m < 2 ^ 256) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializerFinish s accumulatorWord count b e m baseOff expOff
      rest hcap hm hcode hfork hrun hnp).cost +
        MachineState.memCost
          (serializerLoop s accumulatorWord count b e m baseOff expOff rest
            m).activeWords.toNat =
      35 + MachineState.memCost
        (bigReturned s accumulatorWord count b e m baseOff expOff rest).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerGuardPath 26
        (run_serializerFinishGuard s accumulatorWord count b e m baseOff expOff
          rest (by omega) hm hcode hrun)
        (by simpa [serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hreturn :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerReturnPath 9
        (run_serializerReturn s accumulatorWord count b e m baseOff expOff rest
          (by omega) hm hrun)
        (by simpa [serializerExit, serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  unfold gasSteps_serializerFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [serializerLoop, serializerExit, bigReturned] at hguard hreturn ⊢
  omega

def gasSteps_serializeResult (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (he : e < 2 ^ 256) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulatorWord count b e m baseOff expOff rest e)
      (bigReturned s accumulatorWord count b e m baseOff expOff rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka outerFinishGuardPath
      (by simpa [outerLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [outerLoop, State.fork] using hfork)
      (run_outerFinishGuard s accumulatorWord count b e m baseOff expOff rest
        (by omega) he hcode hrun)
      (by simpa [outerLoop] using hrun)
      (by simpa [outerLoop, State.fork] using hnp)
  have hentry := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka serializerEntryPath
      (by simpa [serializerEntry, Artifact.referenceArtifact] using hcode)
      (by simpa [serializerEntry, State.fork] using hfork)
      (run_serializerEntry s accumulatorWord count b e m baseOff expOff rest
        (by omega) hrun)
      (by simpa [serializerEntry] using hrun)
      (by simpa [serializerEntry, State.fork] using hnp)
  have hloop := gasSteps_serializerLoop s accumulatorWord count b e m baseOff
    expOff rest hcap hm hcode hfork hrun hnp
  have hfinish := gasSteps_serializerFinish s accumulatorWord count b e m
    baseOff expOff rest hcap hm hcode hfork hrun hnp
  exact Challenge.EvmProof.GasSteps.cast
    (hguard.trans (hentry.trans (hloop.trans hfinish))) rfl rfl

theorem gasSteps_serializeResult_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (he : e < 2 ^ 256) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializeResult s accumulatorWord count b e m baseOff expOff rest
      hcap he hm hcode hfork hrun hnp).cost +
        MachineState.memCost
          (outerLoop s accumulatorWord count b e m baseOff expOff rest
            e).activeWords.toNat =
      (66 + m * 138) + MachineState.memCost
        (bigReturned s accumulatorWord count b e m baseOff expOff rest).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      outerFinishGuardPath 26
        (run_outerFinishGuard s accumulatorWord count b e m baseOff expOff rest
          (by omega) he hcode hrun)
        (by simpa [outerLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hentry :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerEntryPath 5
        (run_serializerEntry s accumulatorWord count b e m baseOff expOff rest
          (by omega) hrun)
        (by simpa [serializerEntry, State.fork] using hfork)
        (by decide) (by decide)
  have hloop := gasSteps_serializerLoop_cost_potential s accumulatorWord count b
    e m baseOff expOff rest hcap hm hcode hfork hrun hnp
  have hfinish := gasSteps_serializerFinish_cost_potential s accumulatorWord
    count b e m baseOff expOff rest hcap hm hcode hfork hrun hnp
  unfold gasSteps_serializeResult
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [outerLoop, exponentOuterExit, serializerEntry, serializerLoop,
    bigReturned] at hguard hentry hloop hfinish ⊢
  omega

end Challenge.Modexp.Reference.Proofs.Bytecode.BigSerialize
