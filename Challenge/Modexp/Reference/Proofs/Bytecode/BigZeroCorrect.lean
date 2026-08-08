import Challenge.Modexp.Reference.Proofs.Bytecode.BigSerializeCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of the multi-limb zero-modulus exit -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigZeroCorrect

open EvmSemantics
open EvmSemantics.EVM

theorem getByte_zero_of_readWord_zero (memory : ByteArray) (start rem : Nat)
    (hrem : rem < 32) (hword : MachineState.readWord memory start = 0) :
    memory[start + rem]?.getD 0 = 0 := by
  have hwhole : Precompile.bytesToNatPadded memory start 32 = 0 := by
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, hword]
    rfl
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add memory start
    (rem + 1) (31 - rem)
  have hsum : rem + 1 + (31 - rem) = 32 := by omega
  rw [hsum, hwhole] at hsplit
  have hpow : 0 < 256 ^ (31 - rem) := pow_pos (by omega) _
  have hprefix : Precompile.bytesToNatPadded memory start (rem + 1) = 0 := by
    have hmul := (Nat.add_eq_zero_iff.mp hsplit.symm).1
    exact (Nat.mul_eq_zero.mp hmul).resolve_right (Nat.ne_of_gt hpow)
  have hsucc := Challenge.EvmProof.Bytes.bytesToNatPadded_succ memory start rem
  rw [hprefix] at hsucc
  have hbyteNat :
      (YulSemantics.EVM.byteFrom memory.toList (start + rem)).toNat = 0 := by
    omega
  have hbyte : YulSemantics.EVM.byteFrom memory.toList (start + rem) = 0 := by
    apply UInt8.toNat_inj.mp
    simpa using hbyteNat
  have hmatch := Challenge.EvmProof.Bytes.memMatch_toList memory (start + rem)
  rw [hbyte] at hmatch
  by_cases hin : start + rem < memory.size
  · rw [dif_pos hin] at hmatch
    rw [Challenge.EvmProof.Memory.getD0_eq_getElem!]
    rw [getElem!_pos memory (start + rem) hin]
    exact hmatch.symm
  · rw [dif_neg hin] at hmatch
    exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le memory
      (start + rem) (by omega)

theorem readPadded_zero_of_represents (memory : ByteArray)
    (ptr count width : Nat) (hwidth : width ≤ 32 * count)
    (hrep : Limbs.Represents memory ptr count 0) :
    MachineState.readPadded memory ptr width = Precompile.natToBytes 0 width := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size, Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < width := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    let limb := k / 32
    let rem := k % 32
    have hlimb : limb < count := by
      simp only [limb]
      omega
    have hrem : rem < 32 := by
      exact Nat.mod_lt _ (by omega)
    have hwordNat := BigSerializeCorrect.readLimb_of_represents hrep hlimb
    have hword : MachineState.readWord memory (ptr + 32 * limb) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      have hzeroNat : (0 : UInt256).toNat = 0 := by decide
      rw [hzeroNat]
      simpa using hwordNat
    have hbyte := getByte_zero_of_readWord_zero memory (ptr + 32 * limb) rem
      hrem hword
    have hrecompose : 32 * limb + rem = k := by
      have h := Nat.mod_add_div k 32
      simp only [limb, rem]
      omega
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk,
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD 0 width k hk]
    simpa [hrecompose, Nat.add_assoc] using hbyte

theorem setupReturned_output_zero (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hmBound : m ≤ 1024)
    (hmodOff : modOff < 2 ^ 256) :
    Limbs.Represents
      (BigSetup.setupReturned s b e m baseOff expOff modOff returnDest rest).memory
      6144 (Limbs.limbCount m) 0 := by
  let n := Limbs.limbCount m
  let s2 := BigSetup.afterClear2048 s b e m baseOff expOff modOff returnDest rest
  let s3 := BigSetup.afterClear6144 s b e m baseOff expOff modOff returnDest rest
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hm : m < 2 ^ 256 := by omega
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h6144 : (6144 : UInt256) = UInt256.ofNat 6144 := by decide
  have hmNat : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hm]
  have hmodOffNat : (UInt256.ofNat modOff).toNat = modOff := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodOff]
  have hz : Limbs.Represents s3.memory 6144 n 0 := by
    simpa [s3, BigSetup.afterClear6144, BigHelpers.clearReturned, h6144]
      using BigHelpers.clearMemory_represents_zero s2.memory 6144 n (by omega)
  have hkeep := BigBaseCorrect.loadMemory_preserves_region
    s3.executionEnv.calldata s3.memory modOff 0 m m 6144 n 0 (by omega) hm
    (by omega) (by omega) hz
  simpa [BigSetup.setupReturned, s3, BigLoad.loadReturned,
    BigLoad.loadLoop, h0, hmNat, hmodOffNat, n] using hkeep

def zeroFinalState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let loaded := BigComplete.setupState s b e m baseOff expOff modOff
    returnDest rest
  BigModulus.scanZeroFinal loaded (Limbs.limbCount m) b e m baseOff expOff
    modOff returnDest rest

theorem setupState_modulus_represents (input : ByteArray)
    (returnDest : UInt256) (rest : List UInt256) (hvalid : ValidInput input) :
    let b := baseSize input
    let e := exponentSize input
    let m := modulusSize input
    let expOff := Word.expOffset input
    let modOff := Word.modulusOffset input
    let loaded := BigComplete.setupState (Main.headerState input) b e m 96
      expOff modOff returnDest rest
    Limbs.Represents loaded.memory 0 (Limbs.limbCount m)
      (Word.modulusValue input) := by
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := Word.expOffset input
  let modOff := Word.modulusOffset input
  let loaded := BigComplete.setupState (Main.headerState input) b e m 96
    expOff modOff returnDest rest
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hmodOff : modOff < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb, he, _⟩
    simp only [modOff, Word.modulusOffset, Word.expOffset]
    omega
  have hraw := BigSetup.setupReturned_modulus_represents
    (Main.headerState input) b e m 96 expOff modOff returnDest rest hm hmodOff
  rw [show (Main.headerState input).executionEnv.calldata = input by rfl] at hraw
  simpa [loaded, BigComplete.setupState, b, e, m, expOff, modOff,
    Word.modulusValue, Word.modulusOffset] using hraw

theorem modulusOr_eq_zero_iff (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input) :
    BigComplete.modulusOr (Main.headerState input) (baseSize input)
        (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
        (Word.modulusOffset input) returnDest rest = 0 ↔
      Word.modulusValue input = 0 := by
  let loaded := BigComplete.setupState (Main.headerState input) (baseSize input)
    (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
    (Word.modulusOffset input) returnDest rest
  have hrep := setupState_modulus_represents input returnDest rest hvalid
  simpa [BigComplete.modulusOr, BigComplete.limbCount, loaded,
    BigComplete.setupState] using
      BigModulus.scanOr_eq_zero_iff_value_eq_zero loaded.memory
        (Limbs.limbCount (modulusSize input)) (Word.modulusValue input)
        (by simpa [loaded] using hrep)

theorem zeroFinalState_hReturn (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulus : Word.modulusValue input = 0) :
    (zeroFinalState (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) returnDest rest).hReturn = spec input := by
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := Word.expOffset input
  let modOff := Word.modulusOffset input
  let loaded := BigComplete.setupState (Main.headerState input) b e m 96 expOff
    modOff returnDest rest
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hmodOff : modOff < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb, he, _⟩
    simp only [modOff, Word.modulusOffset, Word.expOffset]
    omega
  have hzero := setupReturned_output_zero (Main.headerState input) b e m 96
    expOff modOff returnDest rest hm hmodOff
  have hbytes := readPadded_zero_of_represents loaded.memory 6144
    (Limbs.limbCount m) m (Limbs.width_le_limbs m)
    (by simpa [loaded, BigComplete.setupState] using hzero)
  have hmodulus' : Precompile.bytesToNatPadded input
      (96 + baseSize input + exponentSize input) (modulusSize input) = 0 := by
    simpa [Word.modulusValue, Word.modulusOffset, Word.expOffset,
      Nat.add_assoc] using hmodulus
  rw [spec, if_neg (by omega), hmodulus']
  simpa [zeroFinalState, loaded, b, e, m, expOff, modOff,
    BigModulus.scanZeroFinal, Precompile.modPow] using hbytes

theorem zeroFinalState_result (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulus : Word.modulusValue input = 0) :
    (zeroFinalState (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) returnDest rest).toResult =
        .returned (spec input) := by
  rw [State.toResult_returned _ (by rfl),
    zeroFinalState_hReturn input returnDest rest hvalid hbig hmodulus]

def gasSteps_zero (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hmBound : m ≤ 1024) (hmodOff : modOff < 2 ^ 256)
    (hinputFit : modOff + m ≤ 2 ^ 256) (hcap : rest.length < 992)
    (hor : BigComplete.modulusOr s b e m baseOff expOff modOff returnDest
      rest = 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigSetup.setupEntry s b e m baseOff expOff modOff returnDest rest)
      (zeroFinalState s b e m baseOff expOff modOff returnDest rest) := by
  let n := Limbs.limbCount m
  let loaded := BigComplete.setupState s b e m baseOff expOff modOff
    returnDest rest
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hsetup := BigSetup.gasSteps_setup s b e m baseOff expOff modOff
    returnDest rest hmBound hmodOff hinputFit hcap hcode hfork hrun hnp
  have hscan := BigModulus.gasSteps_scanZeroTotal loaded n b e m baseOff expOff
    modOff returnDest rest (by omega) hn (by omega)
    (by simpa [BigComplete.modulusOr, BigComplete.limbCount, loaded,
      BigComplete.setupState] using hor)
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  exact Challenge.EvmProof.GasSteps.cast (hsetup.trans hscan) rfl
    (by simp [zeroFinalState, loaded, BigComplete.setupState, n,
      BigComplete.scanRest])

def zeroWork (n m : Nat) : Nat :=
  (343 + n * 284 + m * 190) + (56 + n * 74)

theorem gasSteps_zero_cost_potential (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hmBound : m ≤ 1024)
    (hmodOff : modOff < 2 ^ 256) (hinputFit : modOff + m ≤ 2 ^ 256)
    (hcap : rest.length < 992)
    (hor : BigComplete.modulusOr s b e m baseOff expOff modOff returnDest
      rest = 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_zero s b e m baseOff expOff modOff returnDest rest hmBound
        hmodOff hinputFit hcap hor hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      zeroWork (Limbs.limbCount m) m + MachineState.memCost
        (zeroFinalState s b e m baseOff expOff modOff returnDest rest).activeWords.toNat := by
  let n := Limbs.limbCount m
  let loaded := BigComplete.setupState s b e m baseOff expOff modOff
    returnDest rest
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hs := BigSetup.gasSteps_setup_cost_potential s b e m baseOff expOff
    modOff returnDest rest hmBound hmodOff hinputFit hcap hcode hfork hrun hnp
  have hz := BigModulus.gasSteps_scanZeroTotal_cost_potential loaded n b e m
    baseOff expOff modOff returnDest rest (by omega) hn (by omega)
    (by simpa [BigComplete.modulusOr, BigComplete.limbCount, loaded,
      BigComplete.setupState] using hor)
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  unfold gasSteps_zero
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost]
  simp only [zeroWork, zeroFinalState, n, loaded, BigComplete.setupState] at hs hz ⊢
  omega

end Challenge.Modexp.Reference.Proofs.Bytecode.BigZeroCorrect
