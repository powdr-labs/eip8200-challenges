import Challenge.Bls12381.ProofSupport.FpWordBridge
import Challenge.Bls12381.ProofSupport.FpRepresentation

set_option warningAsError true

/-! # Source-faithful BLS12-381 base-field add/sub/neg schedules -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

def addRaw (a b : Limbs) : Limbs :=
  let sLo := a.lo + b.lo
  let carry := UInt256.lt sLo a.lo
  { hi := a.hi + b.hi + carry, lo := sLo }

def addNeedsCorrection (sum : Limbs) : UInt256 :=
  UInt256.lor (UInt256.gt sum.hi modulusHi)
    (UInt256.land (UInt256.eq sum.hi modulusHi)
      (UInt256.isZero (UInt256.lt sum.lo modulusLo)))

def addCorrect (sum : Limbs) : Limbs :=
  let newLo := sum.lo - modulusLo
  { hi := sum.hi - (modulusHi + UInt256.gt modulusLo sum.lo)
    lo := newLo }

def addSource (a b : Limbs) : Limbs :=
  let sum := addRaw a b
  if (addNeedsCorrection sum).toNat ≠ 0 then addCorrect sum else sum

def subRaw (a b : Limbs) : Limbs :=
  { hi := a.hi - b.hi - UInt256.gt b.lo a.lo
    lo := a.lo - b.lo }

def subRepair (diff : Limbs) : Limbs :=
  let newLo := diff.lo + modulusLo
  { hi := diff.hi + modulusHi + UInt256.lt newLo diff.lo
    lo := newLo }

def subSource (a b : Limbs) : Limbs :=
  let diff := subRaw a b
  if (UInt256.gt diff.hi modulusHi).toNat ≠ 0 then subRepair diff else diff

def negNonzero (a : Limbs) : Limbs :=
  { hi := modulusHi - a.hi - UInt256.gt a.lo modulusLo
    lo := modulusLo - a.lo }

def negSource (a : Limbs) : Limbs :=
  if a.hi.toNat = 0 ∧ a.lo.toNat = 0 then pack 0 else negNonzero a

theorem addNeedsCorrection_eq_wideGeWord (sum : Limbs) :
    addNeedsCorrection sum = Challenge.EvmProof.Limbs.wideGeWord
      (toWide sum) modulusWide := rfl

theorem toWide_addCorrect (sum : Limbs) :
    toWide (addCorrect sum) = Challenge.EvmProof.Limbs.subWide256
      (toWide sum) modulusWide := by
  rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
  constructor
  · apply Challenge.EvmProof.Word.word_ext
    change ((sum.hi.val - (modulusHi.val +
      (UInt256.gt modulusLo sum.lo).val)).val) =
      ((sum.hi.val - modulusHi.val -
        (UInt256.lt sum.lo modulusLo).val).val)
    simp [sub_eq_add_neg, add_assoc, add_comm, UInt256.gt, UInt256.lt]
  · rfl

theorem value_addRaw {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    value (addRaw a b) = value a + value b := by
  have hai := ha.1
  have hbi := hb.1
  have hlow := Challenge.EvmProof.Limbs.addTwo256_value a.lo b.lo
  have habhi : a.hi.toNat + b.hi.toNat < 2 ^ 256 := by
    have hr : 2 ^ 128 + 2 ^ 128 < 2 ^ 256 := by norm_num
    omega
  have hhi : a.hi.toNat + b.hi.toNat +
      (UInt256.lt (a.lo + b.lo) a.lo).toNat <
        Challenge.EvmProof.Limbs.radix := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    have hr : 2 ^ 128 + 2 ^ 128 + 1 <
        Challenge.EvmProof.Limbs.radix := by
      norm_num [Challenge.EvmProof.Limbs.radix]
    split <;> omega
  have hhi' : a.hi.toNat + b.hi.toNat +
      (UInt256.lt (a.lo + b.lo) a.lo).toNat < 2 ^ 256 := by
    simpa [Challenge.EvmProof.Limbs.radix] using hhi
  unfold addRaw value
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [Nat.mod_eq_of_lt habhi, Nat.mod_eq_of_lt hhi']
  change (a.lo + b.lo).toNat + Challenge.EvmProof.Limbs.radix *
      (a.hi.toNat + b.hi.toNat +
        (UInt256.lt (a.lo + b.lo) a.lo).toNat) = _
  change (a.lo + b.lo).toNat + Challenge.EvmProof.Limbs.radix *
      (UInt256.lt (a.lo + b.lo) a.lo).toNat =
    a.lo.toNat + b.lo.toNat at hlow
  calc
    _ = ((a.lo + b.lo).toNat + Challenge.EvmProof.Limbs.radix *
        (UInt256.lt (a.lo + b.lo) a.lo).toNat) +
        Challenge.EvmProof.Limbs.radix *
          (a.hi.toNat + b.hi.toNat) := by ring
    _ = (a.lo.toNat + b.lo.toNat) +
        Challenge.EvmProof.Limbs.radix *
          (a.hi.toNat + b.hi.toNat) := by rw [hlow]
    _ = _ := by ring

theorem value_addSource {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    value (addSource a b) = (value a + value b) %
      EvmSemantics.Crypto.Bls12381.p := by
  have hp0 : 0 < EvmSemantics.Crypto.Bls12381.p := by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  have htotal : value a + value b <
      2 * EvmSemantics.Crypto.Bls12381.p := by
    have hava := ha.2
    have havb := hb.2
    omega
  have hraw := value_addRaw ha hb
  unfold addSource
  let sum := addRaw a b
  by_cases hc : (addNeedsCorrection sum).toNat ≠ 0
  · rw [if_pos hc]
    have hge : EvmSemantics.Crypto.Bls12381.p ≤ value sum := by
      rw [addNeedsCorrection_eq_wideGeWord] at hc
      exact (Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff _ _).mp hc
    have hcorrect := congrArg Challenge.EvmProof.Limbs.WideProduct.value
      (toWide_addCorrect sum)
    rw [toWide_value, Challenge.EvmProof.Limbs.subWide256_value,
      modulusWide_value, toWide_value, if_pos hge] at hcorrect
    have hsum : value sum = value a + value b := hraw
    rw [hsum] at hge hcorrect
    have hred : value a + value b - EvmSemantics.Crypto.Bls12381.p <
        EvmSemantics.Crypto.Bls12381.p := by omega
    rw [hcorrect, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hred]
  · rw [if_neg hc, hraw]
    have hlt : value a + value b < EvmSemantics.Crypto.Bls12381.p := by
      have hnge : ¬EvmSemantics.Crypto.Bls12381.p ≤ value sum := by
        intro hge
        apply hc
        rw [addNeedsCorrection_eq_wideGeWord]
        exact (Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff _ _).mpr hge
      rw [hraw] at hnge
      omega
    exact (Nat.mod_eq_of_lt hlt).symm

theorem toWide_subRaw (a b : Limbs) :
    toWide (subRaw a b) = Challenge.EvmProof.Limbs.subWide256
      (toWide a) (toWide b) := rfl

theorem toWide_subRepair (diff : Limbs) :
    toWide (subRepair diff) = Challenge.EvmProof.Limbs.addWide256
      (toWide diff) modulusWide := rfl

theorem value_subRepair (diff : Limbs) :
    value (subRepair diff) =
      (value diff + EvmSemantics.Crypto.Bls12381.p) %
        Challenge.EvmProof.Limbs.radix ^ 2 := by
  have hwide := congrArg Challenge.EvmProof.Limbs.WideProduct.value
    (toWide_subRepair diff)
  rw [toWide_value, Challenge.EvmProof.Limbs.addWide256_value_mod,
    toWide_value, modulusWide_value] at hwide
  exact hwide

theorem subRepairCondition_iff {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b) :
    (UInt256.gt (subRaw a b).hi modulusHi).toNat ≠ 0 ↔ value a < value b := by
  let diff := subRaw a b
  have hword : (UInt256.gt diff.hi modulusHi).toNat ≠ 0 ↔
      modulusHi.toNat < diff.hi.toNat := by
    rw [Challenge.EvmProof.Word.word_toNat_gt]
    by_cases hgt : modulusHi.toNat < diff.hi.toNat <;> simp [hgt]
  rw [hword]
  have hraw := congrArg Challenge.EvmProof.Limbs.WideProduct.value
    (toWide_subRaw a b)
  rw [toWide_value, Challenge.EvmProof.Limbs.subWide256_value,
    toWide_value, toWide_value] at hraw
  have hdiffLo : diff.lo.toNat < Challenge.EvmProof.Limbs.radix :=
    diff.lo.val.isLt
  have hpLo : modulusLo.toNat < Challenge.EvmProof.Limbs.radix :=
    modulusLo.val.isLt
  have hpBelowNext : EvmSemantics.Crypto.Bls12381.p <
      Challenge.EvmProof.Limbs.radix * (modulusHi.toNat + 1) := by
    calc
      _ = modulusLo.toNat +
          Challenge.EvmProof.Limbs.radix * modulusHi.toNat := modulus_words.symm
      _ < Challenge.EvmProof.Limbs.radix +
          Challenge.EvmProof.Limbs.radix * modulusHi.toNat :=
        Nat.add_lt_add_right hpLo _
      _ = _ := by ring
  have hgap : Challenge.EvmProof.Limbs.radix * (modulusHi.toNat + 1) <
      Challenge.EvmProof.Limbs.radix ^ 2 -
        EvmSemantics.Crypto.Bls12381.p := by
    norm_num [modulusHi, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Limbs.radix, EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  by_cases hle : value b ≤ value a
  · rw [if_pos hle] at hraw
    constructor
    · intro hgt
      have hmul : Challenge.EvmProof.Limbs.radix *
          (modulusHi.toNat + 1) ≤
            Challenge.EvmProof.Limbs.radix * diff.hi.toNat :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hgt)
      have hdiffGe : Challenge.EvmProof.Limbs.radix * diff.hi.toNat ≤
          value diff := by
        unfold value
        omega
      have hdiffLt : value diff < EvmSemantics.Crypto.Bls12381.p := by
        rw [hraw]
        exact (Nat.sub_le _ _).trans_lt ha.2
      omega
    · intro hlt
      omega
  · have hlt : value a < value b := by omega
    rw [if_neg hle] at hraw
    constructor
    · intro _
      exact hlt
    · intro _
      by_contra hnhi
      have hhi : diff.hi.toNat ≤ modulusHi.toNat := by omega
      have hmul : Challenge.EvmProof.Limbs.radix * diff.hi.toNat ≤
          Challenge.EvmProof.Limbs.radix * modulusHi.toNat :=
        Nat.mul_le_mul_left _ hhi
      have hdiffUpper : value diff <
          Challenge.EvmProof.Limbs.radix * (modulusHi.toNat + 1) := by
        have hloLe : diff.lo.toNat ≤ Challenge.EvmProof.Limbs.radix - 1 :=
          Nat.le_pred_of_lt hdiffLo
        calc
          value diff = diff.lo.toNat +
              Challenge.EvmProof.Limbs.radix * diff.hi.toNat := rfl
          _ ≤ (Challenge.EvmProof.Limbs.radix - 1) +
              Challenge.EvmProof.Limbs.radix * modulusHi.toNat :=
            Nat.add_le_add hloLe hmul
          _ < Challenge.EvmProof.Limbs.radix +
              Challenge.EvmProof.Limbs.radix * modulusHi.toNat :=
            Nat.add_lt_add_right
              (Nat.sub_lt Challenge.EvmProof.Limbs.radix_pos (by omega)) _
          _ = _ := by ring
      have hdiffLower : Challenge.EvmProof.Limbs.radix ^ 2 -
          EvmSemantics.Crypto.Bls12381.p < value diff := by
        have hbSq : value b < Challenge.EvmProof.Limbs.radix ^ 2 :=
          hb.2.trans p_lt_radix_sq
        have hsub : Challenge.EvmProof.Limbs.radix ^ 2 -
            EvmSemantics.Crypto.Bls12381.p <
              Challenge.EvmProof.Limbs.radix ^ 2 - value b :=
          Nat.sub_lt_sub_left hbSq hb.2
        have hadd : Challenge.EvmProof.Limbs.radix ^ 2 - value b ≤
            Challenge.EvmProof.Limbs.radix ^ 2 + value a - value b :=
          Nat.sub_le_sub_right (Nat.le_add_right _ _) _
        rw [hraw]
        exact hsub.trans_le hadd
      omega

theorem value_subSource {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    value (subSource a b) =
      (EvmSemantics.Crypto.Bls12381.p + value a - value b) %
        EvmSemantics.Crypto.Bls12381.p := by
  let diff := subRaw a b
  have hcondition := subRepairCondition_iff ha hb
  have hraw := congrArg Challenge.EvmProof.Limbs.WideProduct.value
    (toWide_subRaw a b)
  rw [toWide_value, Challenge.EvmProof.Limbs.subWide256_value,
    toWide_value, toWide_value] at hraw
  unfold subSource
  change value (if (UInt256.gt diff.hi modulusHi).toNat ≠ 0 then
      subRepair diff else diff) = _
  by_cases hlt : value a < value b
  · have hrepair := hcondition.mpr hlt
    rw [if_pos hrepair, value_subRepair]
    have hnle : ¬value b ≤ value a := by omega
    rw [if_neg hnle] at hraw
    have hbvalue := hb.2
    have hresidual : EvmSemantics.Crypto.Bls12381.p + value a - value b <
        EvmSemantics.Crypto.Bls12381.p := by omega
    have hresidualSq : EvmSemantics.Crypto.Bls12381.p + value a - value b <
        Challenge.EvmProof.Limbs.radix ^ 2 :=
      hresidual.trans p_lt_radix_sq
    have hsum : value diff + EvmSemantics.Crypto.Bls12381.p =
        Challenge.EvmProof.Limbs.radix ^ 2 +
          (EvmSemantics.Crypto.Bls12381.p + value a - value b) := by
      have hbSq : value b < Challenge.EvmProof.Limbs.radix ^ 2 :=
        hb.2.trans p_lt_radix_sq
      rw [hraw]
      omega
    have hmod := Challenge.EvmProof.Limbs.residual_eq_mod_of_eq_add
      hsum hresidualSq
    rw [← hmod, Nat.mod_eq_of_lt hresidual]
  · have hkeep : ¬(UInt256.gt diff.hi modulusHi).toNat ≠ 0 := by
      intro hrepair
      exact hlt (hcondition.mp hrepair)
    rw [if_neg hkeep]
    have hle : value b ≤ value a := by omega
    rw [if_pos hle] at hraw
    rw [hraw]
    have hresidual : value a - value b < EvmSemantics.Crypto.Bls12381.p :=
      (Nat.sub_le _ _).trans_lt ha.2
    have hsum : EvmSemantics.Crypto.Bls12381.p + value a - value b =
        EvmSemantics.Crypto.Bls12381.p + (value a - value b) := by omega
    rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_mod]
    exact (Nat.mod_eq_of_lt hresidual).symm

theorem toWide_negNonzero (a : Limbs) :
    toWide (negNonzero a) = Challenge.EvmProof.Limbs.subWide256
      modulusWide (toWide a) := rfl

theorem value_negSource {a : Limbs} (ha : Canonical a) :
    value (negSource a) =
      (EvmSemantics.Crypto.Bls12381.p - value a) %
        EvmSemantics.Crypto.Bls12381.p := by
  unfold negSource
  by_cases hzero : a.hi.toNat = 0 ∧ a.lo.toNat = 0
  · rw [if_pos hzero]
    have havalue : value a = 0 := by simp [value, hzero.1, hzero.2]
    rw [value_pack (by
      norm_num [Challenge.EvmProof.Limbs.radix]), havalue]
    simp
  · rw [if_neg hzero]
    have hapos : 0 < value a := by
      unfold value
      have hr := Challenge.EvmProof.Limbs.radix_pos
      by_cases hhi : a.hi.toNat = 0
      · have hlo : 0 < a.lo.toNat := by omega
        omega
      · have hterm : 0 < Challenge.EvmProof.Limbs.radix * a.hi.toNat :=
          Nat.mul_pos hr (Nat.pos_of_ne_zero hhi)
        omega
    have hwide := congrArg Challenge.EvmProof.Limbs.WideProduct.value
      (toWide_negNonzero a)
    rw [toWide_value, Challenge.EvmProof.Limbs.subWide256_value,
      modulusWide_value, toWide_value, if_pos ha.2.le] at hwide
    have havalueLt := ha.2
    have hred : EvmSemantics.Crypto.Bls12381.p - value a <
        EvmSemantics.Crypto.Bls12381.p := by omega
    rw [hwide, Nat.mod_eq_of_lt hred]

theorem canonical_addSource {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b) : Canonical (addSource a b) := by
  apply canonical_of_value_lt
  rw [value_addSource ha hb]
  exact Nat.mod_lt _ (by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])

theorem canonical_negSource {a : Limbs} (ha : Canonical a) :
    Canonical (negSource a) := by
  apply canonical_of_value_lt
  rw [value_negSource ha]
  exact Nat.mod_lt _ (by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])

theorem canonical_subSource {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b) : Canonical (subSource a b) := by
  apply canonical_of_value_lt
  rw [value_subSource ha hb]
  exact Nat.mod_lt _ (by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])

theorem toField_addSource {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b) : toField (addSource a b) = toField a + toField b := by
  apply Fin.ext
  simp only [toField, Fin.add_def, Fin.val_ofNat]
  rw [value_addSource ha hb]
  simp [Nat.add_mod]

theorem toField_negSource {a : Limbs} (ha : Canonical a) :
    toField (negSource a) = -toField a := by
  apply Fin.ext
  simp only [toField, Fin.neg_def, Fin.val_ofNat]
  rw [value_negSource ha]
  rw [Nat.mod_mod, Nat.mod_eq_of_lt ha.2]

theorem toField_subSource {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b) : toField (subSource a b) = toField a - toField b := by
  apply Fin.ext
  simp only [toField, Fin.sub_def, Fin.val_ofNat]
  rw [value_subSource ha hb]
  simp only [Nat.mod_mod]
  rw [Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hb.2]
  by_cases hbzero : value b = 0
  · simp [hbzero]
  · have hbvalue := hb.2
    congr 1
    omega

end Challenge.Bls12381.ProofSupport.Fp
