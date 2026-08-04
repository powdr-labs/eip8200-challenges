import Challenge.Sha256.Reference.Proofs.Bytecode.Functions
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Certified summaries for the reference SHA-256 big-sigma functions

The compiled helpers call the common rotate-right routine three times.  This
file certifies the concrete setup and finishing basic blocks, then composes
them with `Functions.gasSteps_rotr` into reusable function summaries.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.BigSigma

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def bigSigma0SetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨79, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨80, .push ⟨2, by decide⟩ (UInt256.ofNat 126), by rfl, by decide⟩,
   ⟨81, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨82, .push ⟨1, by decide⟩ (UInt256.ofNat 22), by rfl, by decide⟩,
   ⟨83, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨84, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨85, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma0Middle1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨86, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨87, .push ⟨2, by decide⟩ (UInt256.ofNat 138), by rfl, by decide⟩,
   ⟨88, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨89, .push ⟨1, by decide⟩ (UInt256.ofNat 13), by rfl, by decide⟩,
   ⟨90, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨91, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨92, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma0Middle2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨93, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨94, .push ⟨2, by decide⟩ (UInt256.ofNat 150), by rfl, by decide⟩,
   ⟨95, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨96, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨97, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨98, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨99, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma0FinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨100, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨101, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨102, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨103, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨104, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨105, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨106, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨107, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma1SetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨111, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨112, .push ⟨2, by decide⟩ (UInt256.ofNat 175), by rfl, by decide⟩,
   ⟨113, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨114, .push ⟨1, by decide⟩ (UInt256.ofNat 25), by rfl, by decide⟩,
   ⟨115, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨116, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨117, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma1Middle1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨118, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨119, .push ⟨2, by decide⟩ (UInt256.ofNat 187), by rfl, by decide⟩,
   ⟨120, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨121, .push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨122, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨123, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨124, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma1Middle2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨125, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨126, .push ⟨2, by decide⟩ (UInt256.ofNat 199), by rfl, by decide⟩,
   ⟨127, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨128, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨129, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨130, .push ⟨2, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨131, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma1FinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨132, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨133, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨134, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨135, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨136, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨137, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨138, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨139, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem bigSigma0PC (i : Nat) (hlo : 79 ≤ i) (hhi : i ≤ 107) :
    Artifact.referenceArtifact.instructionPC i =
      [114, 115, 118, 119, 121, 122, 125, 126, 127, 130,
       131, 133, 134, 137, 138, 139, 142, 143, 145, 146,
       149, 150, 151, 152, 153, 154, 155, 156, 157][i - 79]! := by
  interval_cases i <;> decide

@[simp] private theorem bigSigma1PC (i : Nat) (hlo : 111 ≤ i) (hhi : i ≤ 139) :
    Artifact.referenceArtifact.instructionPC i =
      [163, 164, 167, 168, 170, 171, 174, 175, 176, 179,
       180, 182, 183, 186, 187, 188, 191, 192, 194, 195,
       198, 199, 200, 201, 202, 203, 204, 205, 206][i - 111]! := by
  interval_cases i <;> decide

def afterFirstSetup (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (n returnPC : Nat) : State :=
  Functions.rotrEntry s x n 0 (UInt256.ofNat returnPC)
    (x :: output :: returnDest :: rest)

def afterFirstRotr (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (n returnPC : Nat) : State :=
  Functions.unaryReturned s (Word.evmRotr32 x n) (UInt256.ofNat returnPC)
    (x :: output :: returnDest :: rest)

def afterSecondSetup (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (n1 n2 returnPC : Nat) : State :=
  Functions.rotrEntry s x n2 0 (UInt256.ofNat returnPC)
    (Word.evmRotr32 x n1 :: x :: output :: returnDest :: rest)

def afterSecondRotr (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (n1 n2 returnPC : Nat) : State :=
  Functions.unaryReturned s (Word.evmRotr32 x n2) (UInt256.ofNat returnPC)
    (Word.evmRotr32 x n1 :: x :: output :: returnDest :: rest)

def afterThirdSetup (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (n1 n2 n3 returnPC : Nat) : State :=
  Functions.rotrEntry s x n3 0 (UInt256.ofNat returnPC)
    (Word.evmRotr32 x n2 :: Word.evmRotr32 x n1 ::
      x :: output :: returnDest :: rest)

def afterThirdRotr (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (n1 n2 n3 returnPC : Nat) : State :=
  Functions.unaryReturned s (Word.evmRotr32 x n3) (UInt256.ofNat returnPC)
    (Word.evmRotr32 x n2 :: Word.evmRotr32 x n1 ::
      x :: output :: returnDest :: rest)

set_option linter.unusedSimpArgs false in
theorem run_setup (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (entry n returnPC : Nat) (x output returnDest : UInt256)
    (rest : List UInt256)
    (hmatch : (path = bigSigma0SetupPath ∧ entry = 114 ∧ n = 22 ∧ returnPC = 126) ∨
      (path = bigSigma1SetupPath ∧ entry = 163 ∧ n = 25 ∧ returnPC = 175))
    (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (Functions.unaryEntry s entry x output returnDest rest) =
        some (afterFirstSetup s x output returnDest rest n returnPC) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 4 = true := by decide
  rcases hmatch with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · simp [bigSigma0SetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Functions.unaryEntry, afterFirstSetup, Functions.rotrEntry, List.exchange,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hcode, hrun, hdest]
    rfl
  · simp [bigSigma1SetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Functions.unaryEntry, afterFirstSetup, Functions.rotrEntry, List.exchange,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hcode, hrun, hdest]
    rfl

set_option linter.unusedSimpArgs false in
theorem run_middle1 (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (n1 n2 returnPC : Nat) (x output returnDest : UInt256)
    (rest : List UInt256)
    (hmatch : (path = bigSigma0Middle1Path ∧ n1 = 22 ∧ n2 = 13 ∧ returnPC = 138) ∨
      (path = bigSigma1Middle1Path ∧ n1 = 25 ∧ n2 = 11 ∧ returnPC = 187))
    (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (afterFirstRotr s x output returnDest rest n1
        (if n1 = 22 then 126 else 175)) =
        some (afterSecondSetup s x output returnDest rest n1 n2 returnPC) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 4 = true := by decide
  rcases hmatch with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · simp [bigSigma0Middle1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      afterFirstRotr, afterSecondSetup, Functions.unaryReturned,
      Functions.rotrEntry, List.exchange, hc1, hc2, hc3, hc4, hc5, hc6,
      hc7, hc8, hc9, hcode, hrun, hdest]
    rfl
  · simp [bigSigma1Middle1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      afterFirstRotr, afterSecondSetup, Functions.unaryReturned,
      Functions.rotrEntry, List.exchange, hc1, hc2, hc3, hc4, hc5, hc6,
      hc7, hc8, hc9, hcode, hrun, hdest]
    rfl

set_option linter.unusedSimpArgs false in
theorem run_middle2 (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (n1 n2 n3 returnPC previousPC : Nat)
    (x output returnDest : UInt256) (rest : List UInt256)
    (hmatch : (path = bigSigma0Middle2Path ∧ n1 = 22 ∧ n2 = 13 ∧ n3 = 2 ∧
        returnPC = 150 ∧ previousPC = 138) ∨
      (path = bigSigma1Middle2Path ∧ n1 = 25 ∧ n2 = 11 ∧ n3 = 6 ∧
        returnPC = 199 ∧ previousPC = 187))
    (hcap : rest.length < 1014)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (afterSecondRotr s x output returnDest rest n1 n2 previousPC) =
        some (afterThirdSetup s x output returnDest rest n1 n2 n3 returnPC) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 4 = true := by decide
  rcases hmatch with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [bigSigma0Middle2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      afterSecondRotr, afterThirdSetup, Functions.unaryReturned,
      Functions.rotrEntry, List.exchange, hc1, hc2, hc3, hc4, hc5, hc6,
      hc7, hc8, hc9, hc10, hcode, hrun, hdest]
    rfl
  · simp [bigSigma1Middle2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      afterSecondRotr, afterThirdSetup, Functions.unaryReturned,
      Functions.rotrEntry, List.exchange, hc1, hc2, hc3, hc4, hc5, hc6,
      hc7, hc8, hc9, hc10, hcode, hrun, hdest]
    rfl

set_option linter.unusedSimpArgs false in
theorem run_finish (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (n1 n2 n3 returnPC : Nat) (value : UInt256)
    (x output returnDest : UInt256) (rest : List UInt256)
    (hmatch : (path = bigSigma0FinishPath ∧ n1 = 22 ∧ n2 = 13 ∧ n3 = 2 ∧
        returnPC = 150 ∧ value = Word.evmBigSigma0 x) ∨
      (path = bigSigma1FinishPath ∧ n1 = 25 ∧ n2 = 11 ∧ n3 = 6 ∧
        returnPC = 199 ∧ value = Word.evmBigSigma1 x))
    (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (afterThirdRotr s x output returnDest rest n1 n2 n3 returnPC) =
        some (Functions.unaryReturned s value returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  rcases hmatch with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [bigSigma0FinishPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      afterThirdRotr, Functions.unaryReturned, Word.evmBigSigma0,
      List.exchange, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hcode, hrun, hvalid]
    rfl
  · simp [bigSigma1FinishPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      afterThirdRotr, Functions.unaryReturned, Word.evmBigSigma1,
      List.exchange, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hcode, hrun, hvalid]
    rfl

def gasSteps_bigSigma0 (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (Functions.unaryEntry s 114 x output returnDest rest)
      (Functions.unaryReturned s (Word.evmBigSigma0 x) returnDest rest) := by
  have gSetup : Challenge.EvmProof.GasSteps
      (Functions.unaryEntry s 114 x output returnDest rest)
      (afterFirstSetup s x output returnDest rest 22 126) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma0SetupPath
    · exact hcode
    · exact hfork
    · exact run_setup bigSigma0SetupPath s 114 22 126 x output returnDest rest
        (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gFirst := Functions.gasSteps_rotr s x 22 0 (UInt256.ofNat 126)
    (x :: output :: returnDest :: rest) (by simp; omega) (by decide)
    hcode hfork hrun hnp (by decide)
  have gMiddle1 : Challenge.EvmProof.GasSteps
      (afterFirstRotr s x output returnDest rest 22 126)
      (afterSecondSetup s x output returnDest rest 22 13 138) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma0Middle1Path
    · exact hcode
    · exact hfork
    · simpa using run_middle1 bigSigma0Middle1Path s 22 13 138
        x output returnDest rest (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gSecond := Functions.gasSteps_rotr s x 13 0 (UInt256.ofNat 138)
    (Word.evmRotr32 x 22 :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gMiddle2 : Challenge.EvmProof.GasSteps
      (afterSecondRotr s x output returnDest rest 22 13 138)
      (afterThirdSetup s x output returnDest rest 22 13 2 150) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma0Middle2Path
    · exact hcode
    · exact hfork
    · exact run_middle2 bigSigma0Middle2Path s 22 13 2 150 138
        x output returnDest rest (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gThird := Functions.gasSteps_rotr s x 2 0 (UInt256.ofNat 150)
    (Word.evmRotr32 x 13 :: Word.evmRotr32 x 22 ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gFinish : Challenge.EvmProof.GasSteps
      (afterThirdRotr s x output returnDest rest 22 13 2 150)
      (Functions.unaryReturned s (Word.evmBigSigma0 x) returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma0FinishPath
    · exact hcode
    · exact hfork
    · exact run_finish bigSigma0FinishPath s 22 13 2 150
        (Word.evmBigSigma0 x) x output returnDest rest
        (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by omega)
        hcode hrun hvalid
    · exact hrun
    · exact hnp
  exact gSetup.trans (gFirst.trans
    (gMiddle1.trans (gSecond.trans (gMiddle2.trans (gThird.trans gFinish)))))

def gasSteps_bigSigma1 (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (Functions.unaryEntry s 163 x output returnDest rest)
      (Functions.unaryReturned s (Word.evmBigSigma1 x) returnDest rest) := by
  have gSetup : Challenge.EvmProof.GasSteps
      (Functions.unaryEntry s 163 x output returnDest rest)
      (afterFirstSetup s x output returnDest rest 25 175) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma1SetupPath
    · exact hcode
    · exact hfork
    · exact run_setup bigSigma1SetupPath s 163 25 175 x output returnDest rest
        (Or.inr ⟨rfl, rfl, rfl, rfl⟩) (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gFirst := Functions.gasSteps_rotr s x 25 0 (UInt256.ofNat 175)
    (x :: output :: returnDest :: rest) (by simp; omega) (by decide)
    hcode hfork hrun hnp (by decide)
  have gMiddle1 : Challenge.EvmProof.GasSteps
      (afterFirstRotr s x output returnDest rest 25 175)
      (afterSecondSetup s x output returnDest rest 25 11 187) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma1Middle1Path
    · exact hcode
    · exact hfork
    · simpa using run_middle1 bigSigma1Middle1Path s 25 11 187
        x output returnDest rest (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gSecond := Functions.gasSteps_rotr s x 11 0 (UInt256.ofNat 187)
    (Word.evmRotr32 x 25 :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gMiddle2 : Challenge.EvmProof.GasSteps
      (afterSecondRotr s x output returnDest rest 25 11 187)
      (afterThirdSetup s x output returnDest rest 25 11 6 199) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma1Middle2Path
    · exact hcode
    · exact hfork
    · exact run_middle2 bigSigma1Middle2Path s 25 11 6 199 187
        x output returnDest rest (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gThird := Functions.gasSteps_rotr s x 6 0 (UInt256.ofNat 199)
    (Word.evmRotr32 x 11 :: Word.evmRotr32 x 25 ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have gFinish : Challenge.EvmProof.GasSteps
      (afterThirdRotr s x output returnDest rest 25 11 6 199)
      (Functions.unaryReturned s (Word.evmBigSigma1 x) returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka bigSigma1FinishPath
    · exact hcode
    · exact hfork
    · exact run_finish bigSigma1FinishPath s 25 11 6 199
        (Word.evmBigSigma1 x) x output returnDest rest
        (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by omega)
        hcode hrun hvalid
    · exact hrun
    · exact hnp
  exact gSetup.trans (gFirst.trans
    (gMiddle1.trans (gSecond.trans (gMiddle2.trans (gThird.trans gFinish)))))

end Challenge.Sha256.Reference.Proofs.Bytecode.BigSigma
