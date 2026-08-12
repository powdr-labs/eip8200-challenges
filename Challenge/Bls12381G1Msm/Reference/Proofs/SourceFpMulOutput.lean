import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulCall

set_option warningAsError true

/-! Executable certificate for the two G1MSM `fpMul` output loads. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpMulOutputBlock : Block Op := fpMulBody.drop 7

def fpMulResult (yst : EvmState) (ahi alo bhi blo : U256) : U256 × U256 :=
  (loadWord (fpMulCallState yst ahi alo bhi blo).memory 1280 >>> 128,
   loadWord (fpMulCallState yst ahi alo bhi blo).memory 1296)

def fpMulHighEnv (yst : EvmState) (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpMulInitialEnv ahi alo bhi blo) ["\x0077"]
    [(fpMulResult yst ahi alo bhi blo).1]

def fpMulReturnEnv (yst : EvmState) (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpMulHighEnv yst ahi alo bhi blo) ["\x0078"]
    [(fpMulResult yst ahi alo bhi blo).2]

def fpMulFinalState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  touchMemory (touchMemory (fpMulCallState yst ahi alo bhi blo) 1280 32)
    1296 32

theorem exec_fpMulOutput (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 56 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo)
      (fpMulCallState yst ahi alo bhi blo) fpMulOutputBlock =
    .ok (fpMulReturnEnv yst ahi alo bhi blo,
      fpMulFinalState yst ahi alo bhi blo, .normal) := by
  rw [Interp.execStmts.eq_def]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
