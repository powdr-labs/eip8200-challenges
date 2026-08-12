import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulDefs

set_option warningAsError true

/-! Frozen nested product-and-store boundary for G1MSM `fpMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpMulProductBlock : Block Op :=
  match fpMulStmt0 with
  | .block body => body
  | _ => []

def fpMulProductCallStmt : Stmt Op := fpMulProductBlock[0]!

def fpMulProductStores : Block Op := fpMulProductBlock.drop 1

theorem fpMulStmt0_eq : fpMulStmt0 = .block fpMulProductBlock := by
  rfl

theorem fpMulProductCallStmt_shape : fpMulProductCallStmt =
    .letDecl ["\x0079", "\x0080", "\x0081"]
      (some (.call "\x006"
        [.var "\x0073", .var "\x0074", .var "\x0075", .var "\x0076"])) := by
  rfl

theorem fpMulProductBlock_eq :
    fpMulProductBlock = fpMulProductCallStmt :: fpMulProductStores := by
  rfl

theorem fpMulProductBlock_length : fpMulProductBlock.length = 7 := by
  rfl

theorem fpMulProductStores_length : fpMulProductStores.length = 6 := by
  rfl

theorem hoist_fpMulProductBlock :
    hoist Challenge.EvmProof.modexpExec.toDialect fpMulProductBlock = [] := by
  rfl

def fpMulProductEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0079", (fullMulValue ahi alo bhi blo).r2),
   ("\x0080", (fullMulValue ahi alo bhi blo).r1),
   ("\x0081", (fullMulValue ahi alo bhi blo).r0)] ++
    fpMulInitialEnv ahi alo bhi blo

theorem restore_fpMulProductEnv (ahi alo bhi blo : U256) :
    restore (fpMulInitialEnv ahi alo bhi blo)
      (fpMulProductEnv ahi alo bhi blo) =
    fpMulInitialEnv ahi alo bhi blo := by
  rfl

private def mstoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

def fpMulProductState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  let product := fullMulValue ahi alo bhi blo
  let s0 := mstoreState yst (BitVec.ofNat 256 1024) (BitVec.ofNat 256 96)
  let s1 := mstoreState s0 (BitVec.ofNat 256 1056) (BitVec.ofNat 256 1)
  let s2 := mstoreState s1 (BitVec.ofNat 256 1088) (BitVec.ofNat 256 48)
  let s3 := mstoreState s2 (BitVec.ofNat 256 1120) product.r2
  let s4 := mstoreState s3 (BitVec.ofNat 256 1152) product.r1
  mstoreState s4 (BitVec.ofNat 256 1184) product.r0

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
