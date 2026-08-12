import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveConstant
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveX3

set_option warningAsError true

/-! # Constant-store memory facts for frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private theorem constant_load2432 (yst : EvmState) (x y : U256) :
    loadWord (onCurveStateAfterConstant yst x y).memory 2432 = 0 := by
  unfold onCurveStateAfterConstant
  change loadWord (storeWord (storeWord (storeWord (storeWord
    (onCurveStateAfterX3 yst x y).memory 2432 0) 2464 4) 2496 0) 2528 4)
    2432 = _
  rw [loadWord_storeWord_disjoint _ 2528 2432 _ (by omega),
    loadWord_storeWord_disjoint _ 2496 2432 _ (by omega),
    loadWord_storeWord_disjoint _ 2464 2432 _ (by omega),
    loadWord_storeWord_same]

private theorem constant_load2464 (yst : EvmState) (x y : U256) :
    loadWord (onCurveStateAfterConstant yst x y).memory 2464 = 4 := by
  unfold onCurveStateAfterConstant
  change loadWord (storeWord (storeWord (storeWord (storeWord
    (onCurveStateAfterX3 yst x y).memory 2432 0) 2464 4) 2496 0) 2528 4)
    2464 = _
  rw [loadWord_storeWord_disjoint _ 2528 2464 _ (by omega),
    loadWord_storeWord_disjoint _ 2496 2464 _ (by omega),
    loadWord_storeWord_same]

private theorem constant_load2496 (yst : EvmState) (x y : U256) :
    loadWord (onCurveStateAfterConstant yst x y).memory 2496 = 0 := by
  unfold onCurveStateAfterConstant
  change loadWord (storeWord (storeWord (storeWord (storeWord
    (onCurveStateAfterX3 yst x y).memory 2432 0) 2464 4) 2496 0) 2528 4)
    2496 = _
  rw [loadWord_storeWord_disjoint _ 2528 2496 _ (by omega),
    loadWord_storeWord_same]

private theorem constant_load2528 (yst : EvmState) (x y : U256) :
    loadWord (onCurveStateAfterConstant yst x y).memory 2528 = 4 := by
  unfold onCurveStateAfterConstant
  change loadWord (storeWord (storeWord (storeWord (storeWord
    (onCurveStateAfterX3 yst x y).memory 2432 0) 2464 4) 2496 0) 2528 4)
    2528 = _
  rw [loadWord_storeWord_same]

theorem onCurveConstant_value (yst : EvmState) (x y : U256) :
    fp2At (onCurveStateAfterConstant yst x y) (BitVec.ofNat 256 2432) =
      onCurveTwistB := by
  unfold fp2At onCurveTwistB
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveFour
  have h0 : (BitVec.ofNat 256 2432).toNat = 2432 := by norm_num
  have h32 : (BitVec.ofNat 256 2432 + BitVec.ofNat 256 32).toNat = 2464 := by
    norm_num
  have h64 : (BitVec.ofNat 256 2432 + BitVec.ofNat 256 64).toNat = 2496 := by
    norm_num
  have h96 : (BitVec.ofNat 256 2432 + BitVec.ofNat 256 96).toNat = 2528 := by
    norm_num
  rw [h0, h32, h64, h96]
  rw [constant_load2432, constant_load2464, constant_load2496,
    constant_load2528]
  have hconv0 : YulEvmCompiler.conv (0 : U256) = 0 := by rfl
  have hconv4 : YulEvmCompiler.conv (4 : U256) = 4 := by
    apply YulEvmCompiler.u256ext
    decide
  rw [hconv0, hconv4]

theorem onCurveConstant_x3 (yst : EvmState) (x y : U256) :
    fp2At (onCurveStateAfterConstant yst x y) (BitVec.ofNat 256 2304) =
      fp2At (onCurveStateAfterX3 yst x y) (BitVec.ofNat 256 2304) := by
  apply fp2At_eq_of_loads
  all_goals
    unfold onCurveStateAfterConstant
    change loadWord (storeWord (storeWord (storeWord (storeWord
      (onCurveStateAfterX3 yst x y).memory 2432 0) 2464 4) 2496 0) 2528 4)
      _ = _
    repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by norm_num)]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
