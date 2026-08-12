import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainValidationLawful

set_option warningAsError true

/-! # G2ADD calldata/source-word bridge

The sixteen-word decoder is discharged once here.  Later codec proofs use
`mainDecodedWord_eq_input` and never normalize this nested store graph.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- Every frozen decoded word is exactly its corresponding padded calldata
word. -/
theorem mainDecodedWord_eq_input (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 16) :
    mainDecodedWord yst (32 * i) = wordFrom input.toList (32 * i) := by
  unfold mainDecodedWord
  rw [mainDecodedState_memory, mainDecodedState12_memory,
    mainDecodedState8_memory, mainDecodedState4_memory]
  unfold mainInputWord
  rw [hcalldata]
  interval_cases i <;> norm_num
  all_goals
    repeat' first
      | rw [loadWord_storeWord_disjoint _ _ _ _ (by omega)]
      | rw [loadWord_storeWord_same]

/-- One source-memory Fp2 coordinate.  Concrete projection adapters are kept
at the four EIP offsets, so no modular-address side conditions leak into this
interface. -/
def sourceFp2 (yst : EvmState) (offset : Nat) : Fp2.Repr :=
  fp2At (mainDecodedState yst) (BitVec.ofNat 256 offset)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
