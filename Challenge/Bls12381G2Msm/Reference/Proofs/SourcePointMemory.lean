import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddTotal
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFinitePredicates
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-!
Lawful readback of the fixed high-memory point cells used by G2MSM.

The runtime represents infinity by eight zero words.  A finite point occupies
two canonical `Fp2` values in the following 128-byte halves.  Keeping this
adapter local to the G2MSM proof avoids adding another executable point type.
-/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

/-- Interpret one runtime point cell as the shared lawful affine point. -/
def pointAt (yst : EvmState) (ptr : U256) : G2Affine.Point :=
  if pointZeroValue yst ptr = 0 then
    .affine (Fp2.toLawful (fp2At yst ptr))
      (Fp2.toLawful (fp2At yst (ptr + 128)))
  else .infinity

@[simp] theorem pointAt_of_zero (yst : EvmState) (ptr : U256)
    (hzero : pointZeroValue yst ptr = 0) :
    pointAt yst ptr = .affine (Fp2.toLawful (fp2At yst ptr))
      (Fp2.toLawful (fp2At yst (ptr + 128))) := by
  simp [pointAt, hzero]

@[simp] theorem pointAt_of_infinity (yst : EvmState) (ptr : U256)
    (hinfinity : pointZeroValue yst ptr ≠ 0) :
    pointAt yst ptr = G2Affine.infinity := by
  rw [pointAt, if_neg]
  exact hinfinity

theorem pointAt_storeInfinity_3840 (yst : EvmState) :
    pointAt (msmStoreInfinityState yst 3840) 3840 = G2Affine.infinity := by
  apply pointAt_of_infinity
  simp only [pointZeroValue,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointZeroValue,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2ZeroValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue,
    b2w]
  rw [show (msmStoreInfinityState yst 3840).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 3840 0) 3872 0)
                    3904 0)
                  3936 0)
                3968 0)
              4000 0)
            4032 0)
          4064 0 by
    simpa using msmStoreInfinityState_memory yst 3840]
  simp [loadWord_storeWord_same,
    loadWord_storeWord_disjoint]

theorem msmStorePointState_3840_fp2At_x (yst : EvmState) :
    fp2At (msmStorePointState yst 3840 2688 2944) 3840 =
      fp2At yst 2688 := by
  unfold fp2At Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
  norm_num
  constructor
  · constructor
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          3840 = loadWord yst.memory 2688
      rw [msmStorePointState_memory_3840_2688_2944]
      simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          3872 = loadWord yst.memory 2720
      rw [msmStorePointState_memory_3840_2688_2944]
      simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]
  · constructor
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          3904 = loadWord yst.memory 2752
      rw [msmStorePointState_memory_3840_2688_2944]
      simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          3936 = loadWord yst.memory 2784
      rw [msmStorePointState_memory_3840_2688_2944]
      simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]

theorem msmStorePointState_3840_fp2At_y (yst : EvmState) :
    fp2At (msmStorePointState yst 3840 2688 2944) 3968 =
      fp2At yst 2944 := by
  unfold fp2At Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
  norm_num
  constructor
  · constructor
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          3968 = loadWord yst.memory 2944
      rw [msmStorePointState_memory_3840_2688_2944]
      simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          4000 = loadWord yst.memory 2976
      rw [msmStorePointState_memory_3840_2688_2944]
      simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]
  · constructor
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          4032 = loadWord yst.memory 3008
      rw [msmStorePointState_memory_3840_2688_2944]
      simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]
    · change loadWord (msmStorePointState yst 3840 2688 2944).memory
          4064 = loadWord yst.memory 3040
      rw [msmStorePointState_memory_3840_2688_2944]
      rw [loadWord_storeWord_same]

theorem pointAt_storePoint_3840 (yst : EvmState)
    (hfinite : pointZeroValue
      (msmStorePointState yst 3840 2688 2944) 3840 = 0) :
    pointAt (msmStorePointState yst 3840 2688 2944) 3840 =
      .affine (Fp2.toLawful (fp2At yst 2688))
        (Fp2.toLawful (fp2At yst 2944)) := by
  rw [pointAt_of_zero _ _ hfinite,
    msmStorePointState_3840_fp2At_x]
  norm_num
  rw [msmStorePointState_3840_fp2At_y]

theorem pointAddLeftPointer_eq (yst : EvmState) (out left right : U256) :
    pointAddLeftPointer yst out left right = left := by
  unfold pointAddLeftPointer
  rw [pointAddPrefixState_memory]
  simp [loadWord_storeWord_same, loadWord_storeWord_disjoint]

theorem pointAddRightPointer_eq (yst : EvmState) (out left right : U256) :
    pointAddRightPointer yst out left right = right := by
  unfold pointAddRightPointer pointAddLeftInfinityState
  change loadWord (pointAddPrefixState yst out left right).memory 1984 = right
  rw [pointAddPrefixState_memory]
  simp [loadWord_storeWord_same]

theorem pointAddFiniteStart_memory (yst : EvmState)
    (out left right : U256) :
    (pointAddFiniteStart yst out left right).memory =
      (pointAddPrefixState yst out left right).memory := by
  rfl

theorem pointAddFiniteStart_fp2At_3072 (yst : EvmState)
    (out left right : U256) :
    fp2At (pointAddFiniteStart yst out left right) 3072 = fp2At yst 3072 := by
  unfold fp2At Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
  norm_num
  constructor <;> constructor <;>
    rw [pointAddFiniteStart_memory, pointAddPrefixState_memory] <;>
    simp [loadWord_storeWord_disjoint]

theorem pointAddFiniteStart_fp2At_3840 (yst : EvmState)
    (out left right : U256) :
    fp2At (pointAddFiniteStart yst out left right) 3840 = fp2At yst 3840 := by
  unfold fp2At Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
  norm_num
  constructor <;> constructor <;>
    rw [pointAddFiniteStart_memory, pointAddPrefixState_memory] <;>
    simp [loadWord_storeWord_disjoint]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
