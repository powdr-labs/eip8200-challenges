import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFirstInfinity

set_option warningAsError true

/-! # Frozen G1ADD second-infinity identity branch -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The source statement that returns the first point when the second point is
infinity. -/
def mainSecondInfinityStmt : Stmt Op := mainPointScopeBody[6]!

/-- Exact state produced by the branch's `return(0, 128)`. -/
def mainSecondInfinityReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainValidatedState yst) 0 128 with
    halted := some (.ret, readBytes (mainValidatedState yst).memory 0 128) }

private theorem mainSecondInfinityStmt_shape : mainSecondInfinityStmt =
    .cond (.var "\x0097")
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := by
  rfl

/-- Exact source execution of the second-infinity identity branch. -/
theorem step_mainSecondInfinity_return (yst : EvmState)
    (hsecond : mainInf2 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainSecondInfinityStmt
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt := by
  rw [mainSecondInfinityStmt_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0097")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hzero : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.lit (.number 0)) (.vals [0] (mainValidatedState yst)) := Step.lit
  have hsize : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.lit (.number 128)) (.vals [128] (mainValidatedState yst)) := Step.lit
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 128)])
      (.halt (mainSecondInfinityReturnState yst)) := by
    exact Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil hsize) hzero) rfl
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])]
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt := by
    exact Step.seqStop (Step.exprStmtHalt hret) (by decide)
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt
          (.builtin .ret [.lit (.number 0), .lit (.number 128)])] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])]
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt := by
    simpa [hoist] using hseq
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.block [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])])
      (mainPointEnv yst) (mainSecondInfinityReturnState yst) .halt := by
    have hblock' := Step.block
      (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
    simpa [restore] using hblock'
  exact Step.ifTrue hcondition hsecond hblock

private theorem mainDecodedState_memory_forSecond (yst : EvmState) :
    (mainDecodedState yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 0 (mainInputWord yst 0))
                    32 (mainInputWord yst 32))
                  64 (mainInputWord yst 64))
                96 (mainInputWord yst 96))
              128 (mainInputWord yst 128))
            160 (mainInputWord yst 160))
          192 (mainInputWord yst 192))
        224 (mainInputWord yst 224) := by
  rfl

private theorem mainDecodedState_readInputWindow (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList) :
    readBytes (mainDecodedState yst).memory 0 128 =
      (EvmSemantics.MachineState.readPadded input 0 128).toList := by
  rw [mainDecodedState_memory_forSecond]
  simp only [mainInputWord, hcalldata]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 160 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 128 _ (by omega)]
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 32 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [← Challenge.EvmProof.Bytes.readPadded_toList_add input 64 32 32]
  rw [← Challenge.EvmProof.Bytes.readPadded_toList_add input 32 32 64]
  rw [← Challenge.EvmProof.Bytes.readPadded_toList_add input 0 32 96]

/-- The second-infinity branch returns the exact padded 128-byte calldata
window of the first point. -/
theorem mainSecondInfinity_returned_inputWindow (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (EvmSemantics.MachineState.readPadded input 0 128).toList) := by
  change some (HaltKind.ret,
    readBytes (mainValidatedState yst).memory 0 128) = _
  rw [mainValidatedState_readOutput,
    mainDecodedState_readInputWindow yst input hcalldata]

private theorem decodeG1_left_size {input : ByteArray}
    {left : EvmSemantics.Crypto.Bls12381.Point}
    (hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 =
      some left) : 0 + 128 ≤ input.size := by
  obtain ⟨x, y, _hx, hy, _⟩ :=
    Challenge.Bls12381.ProofSupport.Codec.decodeG1_success_cases hleft
  have hsize :=
    (Challenge.Bls12381.ProofSupport.Codec.decodeFp_eq_some_iff
      input (0 + Challenge.Bls12381.ProofSupport.Codec.fpBytes) y).mp hy |>.1
  simpa [Challenge.Bls12381.ProofSupport.Codec.fpBytes] using hsize

/-- The second-infinity branch returns the exact canonical encoding of the
other decoded point. -/
theorem mainSecondInfinity_returned_other (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (left : EvmSemantics.Crypto.Bls12381.Point)
    (hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 =
      some left) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1 left).toList) := by
  rw [mainSecondInfinity_returned_inputWindow yst input hcalldata]
  rw [Challenge.EvmProof.Bytes.readPadded_eq_extract input 0 128
    (decodeG1_left_size hleft)]
  have hencode :=
    Challenge.Bls12381.ProofSupport.Codec.encodeG1_decodeG1 hleft
  rw [Challenge.Bls12381.ProofSupport.Codec.g1Bytes] at hencode
  rw [← hencode]

/-- The returned point is the local lawful-affine right-identity result. -/
theorem mainSecondInfinity_returned_affineIdentity (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (left : EvmSemantics.Crypto.Bls12381.Point)
    (hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 0 =
      some left) :
    (mainSecondInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (Challenge.Bls12381.ProofSupport.G1Affine.toWire
            (Challenge.Bls12381.ProofSupport.G1Affine.add
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire left)
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire
                (.infinity : EvmSemantics.Crypto.Bls12381.Point))))).toList) := by
  rw [mainSecondInfinity_returned_other yst input hcalldata left hleft]
  congr 3
  have hadd :
      Challenge.Bls12381.ProofSupport.G1Affine.add
          (Challenge.Bls12381.ProofSupport.G1Affine.ofWire left)
          (Challenge.Bls12381.ProofSupport.G1Affine.ofWire
            (.infinity : EvmSemantics.Crypto.Bls12381.Point)) =
        Challenge.Bls12381.ProofSupport.G1Affine.ofWire left := by
    change Challenge.Bls12381.ProofSupport.LawfulAffine.add
        Challenge.Bls12381.ProofSupport.G1Affine.curve
        (Challenge.Bls12381.ProofSupport.G1Affine.ofWire left) .infinity = _
    exact Challenge.Bls12381.ProofSupport.LawfulAffine.add_infinity _ _
  rw [hadd, Challenge.Bls12381.ProofSupport.G1Affine.toWire_ofWire]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
