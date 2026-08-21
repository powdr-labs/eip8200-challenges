import Challenge.Modexp.Reference.Proofs.Yul.BigSetup
import Challenge.Modexp.Reference.Proofs.Yul.BigResult

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Final mathematical composition for the direct MODEXP big path

This module packages the challenge-specific parameters around the reusable
setup, base-conversion, exponentiation, and serialization certificates.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigFinal

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open BigMath

def baseNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 96 (baseSize input)

def exponentOffset (input : ByteArray) : Nat := 96 + baseSize input

def exponentNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (exponentOffset input) (exponentSize input)

@[simp] theorem modulusScanPrefix_env (count : Nat) (st : EvmState) :
    (modulusScanPrefix count st).env = st.env := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [modulusScanPrefix, YulSemantics.EVM.touchMemory] using ih

theorem scratchOneState_calldata (st : EvmState) (m off : U256) :
    (BigPath.scratchOneState st m off).env.calldata = st.env.calldata := by
  simp [BigPath.scratchOneState, BigPath.scratchClearedState,
    BigPath.scannedModulusState, BigPath.loadedModulusState,
    BigPath.clearedOutputState, BigPath.clearedAccumulatorState,
    BigPath.clearedBaseState, BigPath.clearedModulusState,
    BigSetup.clearWordsState_env, BigSetup.loadBigEndianPrefix_env,
    modulusScanPrefix_env, storeWordAt, YulSemantics.EVM.touchMemory]

/-- Under the challenge headers, the source's complete base prelude produces
the reduced base and `1 mod modulus`, while retaining the mathematical
modulus. -/
theorem initializedAccumulatorState_represents (st : EvmState)
    (input : ByteArray) (hcalldata : st.env.calldata = input.toList)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input)
    (hmodulus : BigSetup.modulusNat input ≠ 0) :
    let count := Limbs.limbCount (modulusSize input)
    let modulus := BigSetup.modulusNat input
    let base := baseNat input % modulus
    let initialized := BigPath.initializedAccumulatorState st
      (BitVec.ofNat 256 (baseSize input))
      (BitVec.ofNat 256 (modulusSize input)) 96
      (BitVec.ofNat 256 (BigSetup.modulusOffset input))
    Represents initialized.memory 0x0800 count (1 % modulus) ∧
      Represents initialized.memory 0x0400 count base ∧
      Represents initialized.memory 0x0000 count modulus := by
  let b := baseSize input
  let m := modulusSize input
  let off := BigSetup.modulusOffset input
  let count := Limbs.limbCount m
  let modulus := BigSetup.modulusNat input
  have hb : b ≤ 1024 := hvalid.2.1
  have hm : m ≤ 1024 := hvalid.2.2.2
  have hcount : count ≤ 32 := Limbs.limbCount_le_32 m hm
  have hmodulusPos : 0 < modulus := Nat.pos_of_ne_zero hmodulus
  have hn := BigSetup.limbCount_toNat m hm
  have hsetup := BigSetup.scratchOneState_invariants st input hcalldata hvalid hbig
  have hscratchCalldata :
      (BigPath.scratchOneState st (BitVec.ofNat 256 m)
        (BitVec.ofNat 256 off)).env.calldata = input.toList := by
    rw [scratchOneState_calldata, hcalldata]
  have hbaseFit : (96 : U256).toNat + (BitVec.ofNat 256 b).toNat < 2 ^ 256 := by
    rw [show (96 : U256).toNat = 96 by rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : b < 2 ^ 256)]
    omega
  have hresult := BigResult.initializedAccumulatorState_represents st input
    (BitVec.ofNat 256 b) (BitVec.ofNat 256 m) 96 (BitVec.ofNat 256 off)
    count modulus hn hbaseFit hcount hmodulusPos hscratchCalldata
    hsetup.2.1 hsetup.2.2.1 hsetup.2.2.2 hsetup.1
  have hbWord : (BitVec.ofNat 256 b).toNat = b := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2 ^ 256)]
  rw [hbWord] at hresult
  simpa [b, m, off, count, modulus, baseNat] using hresult

/-- Serialization turns any exponent certificate for the exact source state
into the MODEXP specification bytes.  `BigExponent` supplies `hexponent` by
interpreting the source's nested byte/bit loop. -/
theorem returnedResultState_spec (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input)
    (hexponent : Represents st.memory 0x0800
      (Limbs.limbCount (modulusSize input))
      (Precompile.modPow (baseNat input) (exponentNat input)
        (BigSetup.modulusNat input))) :
    (BigPath.returnedResultState st
      (BitVec.ofNat 256 (modulusSize input))).halted =
      some (HaltKind.ret, (spec input).toList) := by
  have hm : modulusSize input ≤ 1024 := hvalid.2.2.2
  have hserialized := BigResult.returnedResultState_result st
    (modulusSize input)
    (Precompile.modPow (baseNat input) (exponentNat input)
      (BigSetup.modulusNat input)) hm hexponent
  rw [hserialized]
  unfold spec
  rw [if_neg (by omega : modulusSize input ≠ 0)]
  rfl

/-- Exact-state wrapper used to compose the forthcoming complete exponent
certificate with `BigPath`'s nonzero execution endpoint. -/
theorem returnedResultState_nonzero_spec (st : EvmState) (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input)
    (hexponent : Represents
      (BigPath.exponentiatedState st
        (BitVec.ofNat 256 (baseSize input))
        (BitVec.ofNat 256 (exponentSize input))
        (BitVec.ofNat 256 (modulusSize input)) 96
        (BitVec.ofNat 256 (exponentOffset input))
        (BitVec.ofNat 256 (BigSetup.modulusOffset input))).memory
      0x0800 (Limbs.limbCount (modulusSize input))
      (Precompile.modPow (baseNat input) (exponentNat input)
        (BigSetup.modulusNat input))) :
    (BigPath.returnedResultState
      (BigPath.exponentiatedState st
        (BitVec.ofNat 256 (baseSize input))
        (BitVec.ofNat 256 (exponentSize input))
        (BitVec.ofNat 256 (modulusSize input)) 96
        (BitVec.ofNat 256 (exponentOffset input))
        (BitVec.ofNat 256 (BigSetup.modulusOffset input)))
      (BitVec.ofNat 256 (modulusSize input))).halted =
      some (HaltKind.ret, (spec input).toList) :=
  returnedResultState_spec _ input hvalid hbig hexponent

end Challenge.Modexp.Reference.Proofs.Yul.BigFinal
