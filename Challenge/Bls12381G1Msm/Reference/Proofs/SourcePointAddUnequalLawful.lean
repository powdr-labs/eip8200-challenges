import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalBranch
import Challenge.Bls12381G1Add.Reference.Proofs.SourceSub
import Challenge.Bls12381.ProofSupport.FpAddSub

set_option warningAsError true

/-!
Lawful/canonical side conditions for the frozen G1MSM unequal-x path.

The ideal long-term boundary is an upstream lawful-affine API which exports
canonical coordinates together with the concrete memory-region invariant for
an affine point. Until that API is upstreamed, this local adapter keeps both
facts explicit at the source-proof boundary instead of spreading lawful shims
through the execution proof.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def pointAddUnequalLeftXLimbs (yst : EvmState) (out left right : U256) :
    Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddUnequalLeftXHi yst out left right)
    lo := YulEvmCompiler.conv (pointAddUnequalLeftXLo yst out left right) }

def pointAddUnequalRightXLimbs (yst : EvmState) (out left right : U256) :
    Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddUnequalRightXHi yst out left right)
    lo := YulEvmCompiler.conv (pointAddUnequalRightXLo yst out left right) }

theorem pointAddUnequalDenominatorResult_eq_fpSubValue (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalDenominatorResult yst out left right =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
        (pointAddUnequalRightXHi yst out left right)
        (pointAddUnequalRightXLo yst out left right)
        (pointAddUnequalLeftXHi yst out left right)
        (pointAddUnequalLeftXLo yst out left right) := by
  simp only [pointAddUnequalDenominatorResult,
    pointAddUnequalDenominatorRepairValue,
    pointAddUnequalDenominatorRepaired,
    pointAddUnequalDenominatorRaw,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue,
    add_assoc]

theorem pointAddUnequalDenominatorResult_toSource (yst : EvmState)
    (out left right : U256) :
    ({ hi := YulEvmCompiler.conv
          (pointAddUnequalDenominatorResult yst out left right).1
       lo := YulEvmCompiler.conv
          (pointAddUnequalDenominatorResult yst out left right).2 } : Fp.Limbs) =
      Fp.subSource (pointAddUnequalRightXLimbs yst out left right)
        (pointAddUnequalLeftXLimbs yst out left right) := by
  rw [pointAddUnequalDenominatorResult_eq_fpSubValue]
  simpa only [pointAddUnequalLeftXLimbs, pointAddUnequalRightXLimbs,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.convPair]
    using
      (Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubValue
        (pointAddUnequalRightXHi yst out left right)
        (pointAddUnequalRightXLo yst out left right)
        (pointAddUnequalLeftXHi yst out left right)
        (pointAddUnequalLeftXLo yst out left right))

theorem pointAddUnequalDenominatorResult_high_lt_of_canonical
    (yst : EvmState) (out left right : U256)
    (hleft : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hright : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right)) :
    (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128 := by
  have hcanonical := Fp.canonical_subSource hright hleft
  rw [← pointAddUnequalDenominatorResult_toSource yst out left right] at hcanonical
  exact hcanonical.1

theorem step_pointAddUnequalBranch_lawful (yst : EvmState)
    (out left right : U256)
    (hleft : Fp.Canonical (pointAddUnequalLeftXLimbs yst out left right))
    (hright : Fp.Canonical (pointAddUnequalRightXLimbs yst out left right))
    /- The enclosing MSM memory-region invariant supplies this equality. It is
    explicit because `touchMemory` records pointer-dependent high-water marks. -/
    (hstate : pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right) :
    ∃ Vend stend,
      YulSemantics.ExecStmts Challenge.EvmProof.modexpExec.toDialect
        pointAddBodyFuns (pointAddInitialEnv out left right)
        (pointAddXEqState yst out left right) pointAddUnequalBranchCode
        Vend stend .normal :=
  step_pointAddUnequalBranch yst out left right
    (pointAddUnequalDenominatorResult_high_lt_of_canonical
      yst out left right hleft hright) hstate

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
