import Challenge.Bls12381G1Add.Reference.Proofs.SourceMul
import Challenge.EvmProof.ModexpMemory

set_option warningAsError true

/-! # Frozen G1ADD field-memory helpers -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- High source word of the BLS12-381 base-field modulus. -/
def fpModulusHiValue : U256 := BitVec.ofNat 256
  34565483545414906068789196026815425751

/-- Low source word of the BLS12-381 base-field modulus. -/
def fpModulusLoValue : U256 := BitVec.ofNat 256
  45442060874369865957053122457065728162598490762543039060009208264153100167851

/-- State after the exact two-`MSTORE` source schedule that writes a 48-byte
field element starting at `ptr`. -/
def storeFpState (yst : EvmState) (ptr hi lo : U256) : EvmState :=
  let first :=
    { touchMemory yst ptr.toNat 32 with
      memory := storeWord yst.memory ptr.toNat (hi <<< 128) }
  let nextPtr := ptr + BitVec.ofNat 256 16
  { touchMemory first nextPtr.toNat 32 with
    memory := storeWord first.memory nextPtr.toNat lo }

/-- The two `MSTORE`s are the complete memory effect of `storeFp`; memory
touch accounting changes no byte values. -/
theorem storeFpState_memory (ptr hi lo : U256) (yst : EvmState)
    (address : Nat) :
    (storeFpState yst ptr hi lo).memory address =
      storeWord
        (storeWord yst.memory ptr.toNat (hi <<< 128))
        (ptr + BitVec.ofNat 256 16).toNat lo address := by
  rfl

/-- The exact 48-byte window produced by `storeFp` is the big-endian
concatenation of the 128-bit high limb and the 256-bit low limb. -/
theorem bytesNat_readBytes_storeFpState (ptr hi lo : U256) (yst : EvmState)
    (hptr : ptr.toNat + 16 < 2 ^ 256)
    (hhi : hi.toNat < 2 ^ 128) :
    Challenge.EvmProof.Bytes.bytesNat
        (readBytes (storeFpState yst ptr hi lo).memory ptr.toNat 48) =
      hi.toNat * 2 ^ 256 + lo.toNat := by
  have hnext : (ptr + BitVec.ofNat 256 16).toNat = ptr.toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hptr
  have hfirst :
      readBytes
          (storeWord
            (storeWord yst.memory ptr.toNat (hi <<< 128))
            (ptr.toNat + 16) lo)
          ptr.toNat 16 =
        readBytes
          (storeWord yst.memory ptr.toNat (hi <<< 128)) ptr.toNat 16 := by
    unfold readBytes
    apply List.map_congr_left
    intro i hiIndex
    have hiIndex' : i < 16 := by simpa using hiIndex
    simp only [storeWord]
    rw [if_neg]
    omega
  have hshift : (hi <<< 128).toNat / 256 ^ 16 = hi.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hproduct : hi.toNat * 2 ^ 128 < 2 ^ 256 := by
      calc
        hi.toNat * 2 ^ 128 < 2 ^ 128 * 2 ^ 128 :=
          (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ 128)).2 hhi
        _ = 2 ^ 256 := by rw [← pow_add]
    rw [Nat.mod_eq_of_lt hproduct]
    have hpow : 256 ^ 16 = 2 ^ 128 := by
      norm_num [← pow_mul]
    rw [hpow, Nat.mul_comm hi.toNat,
      Nat.mul_div_right _ (by positivity : 0 < 2 ^ 128)]
  have hmemory : (storeFpState yst ptr hi lo).memory =
      storeWord
        (storeWord yst.memory ptr.toNat (hi <<< 128))
        (ptr + BitVec.ofNat 256 16).toNat lo := by
    funext address
    exact storeFpState_memory ptr hi lo yst address
  rw [hmemory, hnext]
  rw [show 48 = 16 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.Bytes.bytesNat_append]
  rw [hfirst]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord_prefix
    yst.memory ptr.toNat 16 (hi <<< 128) (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord]
  simp only [readBytes]
  rw [List.length_map, List.length_range, hshift]
  have hbase : 256 ^ 32 = 2 ^ 256 := by
    norm_num [← pow_mul]
  rw [hbase]

/-- The eighth frozen helper executes the two source-ordered field stores. -/
theorem eval_storeFp (ptr hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("ptr", ptr), ("hi", hi), ("lo", lo)] yst
      (.call "\x007" [.var "ptr", .var "hi", .var "lo"]) =
    .ok (.vals [] (storeFpState yst ptr hi lo)) := by
  rw [Interp.evalExpr]
  rfl

/-- The ninth frozen helper stores the exact BLS12-381 modulus words. -/
theorem eval_storeModulus (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Compilation.referenceCompiledBlock]
      [("ptr", ptr)] yst (.call "\x008" [.var "ptr"]) =
    .ok (.vals [] (storeFpState yst ptr fpModulusHiValue fpModulusLoValue)) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
