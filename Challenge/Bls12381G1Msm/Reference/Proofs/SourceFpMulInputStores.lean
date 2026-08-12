import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulProduct

set_option warningAsError true

/-! Executable certificate for the exponent and modulus stores in `fpMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpMulInputStores : Block Op := (fpMulBody.drop 1).take 5

private def mstoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

private def mstore8State (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 1 with
    memory := storeByte yst.memory offset.toNat value }

def fpMulInputState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  let s0 := mstore8State (fpMulProductState yst ahi alo bhi blo)
    (BitVec.ofNat 256 1216) (BitVec.ofNat 256 1)
  let s1 := mstoreState s0 (BitVec.ofNat 256 1217)
    (BitVec.ofNat 256
      11762024554600535993938308040068522739871412259351471353901582648940435603456)
  mstoreState s1 (BitVec.ofNat 256 1233)
    (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167851)

theorem exec_fpMulInputStores (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 64 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo)
      (fpMulProductState yst ahi alo bhi blo) fpMulInputStores =
    .ok (fpMulInitialEnv ahi alo bhi blo,
      fpMulInputState yst ahi alo bhi blo, .normal) := by
  rw [Interp.execStmts.eq_def]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
