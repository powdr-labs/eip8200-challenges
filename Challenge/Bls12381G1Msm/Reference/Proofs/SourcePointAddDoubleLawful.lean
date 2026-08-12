import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleEqual
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddRefinement
import Challenge.Bls12381.ProofSupport.FpAddSub

set_option warningAsError true

/-!
Lawful/canonical side conditions for the frozen G1MSM doubling path.

The ideal long-term boundary is an upstream lawful-affine API that classifies
equal-x curve points and exposes the canonical limb facts needed by concrete
programs.  Until that API is upstreamed, this local adapter keeps the shim at
the source-proof boundary instead of spreading lawful conversions through the
execution proof.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddFiniteLeftYLimbs (yst : EvmState) (out left right : U256) :
    Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddFiniteLeftYHi yst out left right)
    lo := YulEvmCompiler.conv (pointAddFiniteLeftYLo yst out left right) }

def pointAddFiniteRightYLimbs (yst : EvmState) (out left right : U256) :
    Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddFiniteRightYHi yst out left right)
    lo := YulEvmCompiler.conv (pointAddFiniteRightYLo yst out left right) }

def pointAddDoubleLeftYLimbs (yst : EvmState) (out left right : U256) :
    Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddDoubleLeftYHi yst out left right)
    lo := YulEvmCompiler.conv (pointAddDoubleLeftYLo yst out left right) }

theorem pointAddDoubleDenResult_toSource (yst : EvmState)
    (out left right : U256) :
    ({ hi := YulEvmCompiler.conv
          (pointAddDoubleDenResult yst out left right).1
       lo := YulEvmCompiler.conv
          (pointAddDoubleDenResult yst out left right).2 } : Fp.Limbs) =
      Fp.addSource (pointAddDoubleLeftYLimbs yst out left right)
        (pointAddDoubleLeftYLimbs yst out left right) := by
  simpa only [pointAddDoubleDenResult, pointAddDoubleLeftYLimbs] using
    (fpAddResult_toSource
      (pointAddDoubleLeftYHi yst out left right)
      (pointAddDoubleLeftYLo yst out left right)
      (pointAddDoubleLeftYHi yst out left right)
      (pointAddDoubleLeftYLo yst out left right))

theorem pointAddYSumResult_toSource (yst : EvmState)
    (out left right : U256) :
    ({ hi := YulEvmCompiler.conv (pointAddYSumResult yst out left right).1
       lo := YulEvmCompiler.conv (pointAddYSumResult yst out left right).2 } :
      Fp.Limbs) =
      Fp.addSource (pointAddFiniteLeftYLimbs yst out left right)
        (pointAddFiniteRightYLimbs yst out left right) := by
  simpa only [pointAddYSumResult, pointAddFiniteLeftYLimbs,
    pointAddFiniteRightYLimbs] using
    (fpAddResult_toSource
      (pointAddFiniteLeftYHi yst out left right)
      (pointAddFiniteLeftYLo yst out left right)
      (pointAddFiniteRightYHi yst out left right)
      (pointAddFiniteRightYLo yst out left right))

theorem pointAddDoubleDenResult_high_lt_of_canonical (yst : EvmState)
    (out left right : U256)
    (hy : Fp.Canonical (pointAddDoubleLeftYLimbs yst out left right)) :
    (pointAddDoubleDenResult yst out left right).1.toNat < 2 ^ 128 := by
  have hcanonical := Fp.canonical_addSource hy hy
  rw [← pointAddDoubleDenResult_toSource yst out left right] at hcanonical
  exact hcanonical.1

theorem pointAddYZeroValue_eq_zero_of_lawful_sum (yst : EvmState)
    (out left right : U256)
    (hleft : Fp.Canonical (pointAddFiniteLeftYLimbs yst out left right))
    (hright : Fp.Canonical (pointAddFiniteRightYLimbs yst out left right))
    (hsum : Fp.toField (pointAddFiniteLeftYLimbs yst out left right) +
      Fp.toField (pointAddFiniteRightYLimbs yst out left right) ≠ 0) :
    pointAddYZeroValue yst out left right = 0 := by
  rw [pointAddYZeroValue_eq_zero_iff]
  by_contra hwords
  simp only [not_or, not_not] at hwords
  change (pointAddYSumResult yst out left right).1 = 0 ∧
    (pointAddYSumResult yst out left right).2 = 0 at hwords
  apply hsum
  rw [← Fp.toField_addSource hleft hright,
    ← pointAddYSumResult_toSource yst out left right]
  simp [hwords.1, hwords.2, Fp.toField, Fp.value]

theorem step_pointAddDoubleEqual_lawful (yst : EvmState)
    (out left right : U256)
    (hxeq : pointAddXEqValue yst out left right ≠ 0)
    (hleft : Fp.Canonical (pointAddFiniteLeftYLimbs yst out left right))
    (hright : Fp.Canonical (pointAddFiniteRightYLimbs yst out left right))
    /- The enclosing MSM memory-region invariant supplies this fact.  It is
    intentionally explicit here because arbitrary helper pointers could alias
    the fixed `fpMul` scratch region. -/
    (hdoubleLeft :
      Fp.Canonical (pointAddDoubleLeftYLimbs yst out left right))
    (hsum : Fp.toField (pointAddFiniteLeftYLimbs yst out left right) +
      Fp.toField (pointAddFiniteRightYLimbs yst out left right) ≠ 0) :
    ∃ Vend stend,
      YulSemantics.ExecStmt Challenge.EvmProof.modexpExec.toDialect
        pointAddBodyFuns (pointAddInitialEnv out left right)
        (pointAddFiniteState yst out left right) pointAddStmt5 Vend stend
        .leave := by
  exact step_pointAddDoubleEqual yst out left right hxeq
    (pointAddYZeroValue_eq_zero_of_lawful_sum yst out left right
      hleft hright hsum)
    (pointAddDoubleDenResult_high_lt_of_canonical yst out left right
      hdoubleLeft)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
