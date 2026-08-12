import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvExecDefs

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` MODEXP input state -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

/-- State after the three fixed-size MODEXP headers. -/
def fpInvHeaderState (yst : EvmState) : EvmState :=
  let s0 := mstoreState yst (BitVec.ofNat 256 1024) (BitVec.ofNat 256 48)
  let s1 := mstoreState s0 (BitVec.ofNat 256 1056) (BitVec.ofNat 256 48)
  mstoreState s1 (BitVec.ofNat 256 1088) (BitVec.ofNat 256 48)

/-- State after storing the 48-byte base. -/
def fpInvBaseState (yst : EvmState) (hi lo : U256) : EvmState :=
  storeFpState (fpInvHeaderState yst) (BitVec.ofNat 256 1120) hi lo

/-- State after storing the fixed 48-byte exponent `p - 2`. -/
def fpInvExponentState (yst : EvmState) (hi lo : U256) : EvmState :=
  storeFpState (fpInvBaseState yst hi lo) (BitVec.ofNat 256 1168)
    fpModulusHiValue (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167849)

/-- State immediately before the frozen `fpInv` helper's MODEXP call. The
definition preserves the source header, base, exponent, and modulus stores. -/
def fpInvInputState (yst : EvmState) (hi lo : U256) : EvmState :=
  storeFpState (fpInvExponentState yst hi lo) (BitVec.ofNat 256 1216)
    fpModulusHiValue fpModulusLoValue

/-- Byte-level memory graph for the 240-byte inversion input. -/
theorem fpInvInputState_memory (yst : EvmState) (hi lo : U256) :
    (fpInvInputState yst hi lo).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord
                      (storeWord yst.memory 1024 (BitVec.ofNat 256 48))
                      1056 (BitVec.ofNat 256 48))
                    1088 (BitVec.ofNat 256 48))
                  1120 (hi <<< 128))
                1136 lo)
              1168 (fpModulusHiValue <<< 128))
            1184 (BitVec.ofNat 256
              45442060874369865957053122457065728162598490762543039060009208264153100167849))
          1216 (fpModulusHiValue <<< 128))
        1232 fpModulusLoValue := by
  rfl

def fpInvInput (yst : EvmState) (hi lo : U256) : ByteArray :=
  Challenge.EvmProof.ModexpMemory.readWindow
    (fpInvInputState yst hi lo).memory 1024 240

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
