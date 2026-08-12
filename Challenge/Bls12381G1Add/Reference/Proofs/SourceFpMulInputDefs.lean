import Challenge.Bls12381G1Add.Reference.Proofs.SourceStore

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` MODEXP input state -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

private def mstore8State (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 1 with
    memory := storeByte yst.memory offset.toNat value }

/-- State after the frozen `fpMul` headers, product words, and exponent byte,
but before its two modulus stores. -/
def fpMulPreModulusState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  let product := fullMulValue ahi alo bhi blo
  let s0 := mstoreState yst (BitVec.ofNat 256 1024) (BitVec.ofNat 256 96)
  let s1 := mstoreState s0 (BitVec.ofNat 256 1056) (BitVec.ofNat 256 1)
  let s2 := mstoreState s1 (BitVec.ofNat 256 1088) (BitVec.ofNat 256 48)
  let s3 := mstoreState s2 (BitVec.ofNat 256 1120) product.r2
  let s4 := mstoreState s3 (BitVec.ofNat 256 1152) product.r1
  let s5 := mstoreState s4 (BitVec.ofNat 256 1184) product.r0
  mstore8State s5 (BitVec.ofNat 256 1216) (BitVec.ofNat 256 1)

/-- State immediately before the frozen `fpMul` helper's MODEXP call.  The
definition preserves the exact source store order and offsets. -/
def fpMulInputState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  storeFpState (fpMulPreModulusState yst ahi alo bhi blo)
    (BitVec.ofNat 256 1217) fpModulusHiValue fpModulusLoValue

/-- Byte-level memory graph of the exact `fpMul` input construction. -/
theorem fpMulInputState_memory (yst : EvmState) (ahi alo bhi blo : U256) :
    (fpMulInputState yst ahi alo bhi blo).memory =
      storeWord
        (storeWord
          (storeByte
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord
                      (storeWord yst.memory 1024 (BitVec.ofNat 256 96))
                      1056 (BitVec.ofNat 256 1))
                    1088 (BitVec.ofNat 256 48))
                  1120 (fullMulValue ahi alo bhi blo).r2)
                1152 (fullMulValue ahi alo bhi blo).r1)
              1184 (fullMulValue ahi alo bhi blo).r0)
            1216 (BitVec.ofNat 256 1))
          1217 (fpModulusHiValue <<< 128))
        1233 fpModulusLoValue := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
