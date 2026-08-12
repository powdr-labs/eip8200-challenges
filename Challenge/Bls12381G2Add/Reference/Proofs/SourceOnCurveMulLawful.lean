import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulRight

set_option warningAsError true

/-! # Low-memory lawful endpoint for frozen G2ADD Fp2 products -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- A selected-output contract for the staged frozen `fp2Mul` call with
low-memory inputs and a high scratch output.

The contract deliberately relates the concrete output to the authoritative
source multiplication only after projection to the field. It never asks Lean
to compare the two full reducible representations. -/
structure Fp2MulLowContract (yst : EvmState) (out a b : U256) : Prop where
  evaluated : EvalExpr Challenge.EvmProof.modexpExec.toDialect fp2MulFuns
    [("out", out), ("a", a), ("b", b)] yst
    (.call "\x0016" [.var "out", .var "a", .var "b"])
    (.vals [] (fp2MulFinalState yst out a b))
  output_canonical :
    Fp2.Canonical (fp2At (fp2MulFinalState yst out a b) out)
  output_toField_mulSource :
    Fp2.toField (fp2At (fp2MulFinalState yst out a b) out) =
      Fp2.toField (Fp2.mulSource (fp2At yst a) (fp2At yst b))
  output_toLawful_mul :
    Fp2.toLawful (fp2At (fp2MulFinalState yst out a b) out) =
      Fp2.toLawful (fp2At yst a) * Fp2.toLawful (fp2At yst b)
  lowMemory_preserved : ∀ offset, offset + 32 ≤ 1024 →
    loadWord (fp2MulFinalState yst out a b).memory offset =
      loadWord yst.memory offset

theorem fp2MulFinalState_canonical_of_low (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.Canonical (fp2At (fp2MulFinalState yst out a b) out) := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_low yst a b haEnd haLow
  have hrightInput := fp2MulRightInput_eq_fp2At_of_low yst a b hbEnd hbLow
  apply fp2MulFinalState_canonical yst out a b
  · rwa [hleftInput]
  · rwa [hrightInput]
  · exact fp2MulScheduledLeft_eq_of_low yst out a b haEnd haLow
      houtHigh (by omega)
  · exact fp2MulScheduledRight_eq_of_low yst out a b hbEnd hbLow
      houtHigh (by omega)
  · exact houtHigh
  · exact hout

theorem fp2MulFinalState_toLawful_mul_of_low (yst : EvmState)
    (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2.toLawful (fp2At (fp2MulFinalState yst out a b) out) =
      Fp2.toLawful (fp2At yst a) * Fp2.toLawful (fp2At yst b) := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_low yst a b haEnd haLow
  have hrightInput := fp2MulRightInput_eq_fp2At_of_low yst a b hbEnd hbLow
  rw [← hleftInput, ← hrightInput]
  exact fp2MulFinalState_toLawful_mul yst out a b
    (hleftInput.symm ▸ ha) (hrightInput.symm ▸ hb)
    (fp2MulScheduledLeft_eq_of_low yst out a b haEnd haLow
      houtHigh (by omega))
    (fp2MulScheduledRight_eq_of_low yst out a b hbEnd hbLow
      houtHigh (by omega)) houtHigh hout

/-- Construct the compact consumer contract from the existing staged
execution, locality, and arithmetic summaries. -/
theorem fp2Mul_low_contract (yst : EvmState) (out a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2MulLowContract yst out a b := by
  have hleftInput := fp2MulLeftInput_eq_fp2At_of_low yst a b haEnd haLow
  have hrightInput := fp2MulRightInput_eq_fp2At_of_low yst a b hbEnd hbLow
  have hleftScheduled := fp2MulScheduledLeft_eq_of_low yst out a b haEnd haLow
    houtHigh (by omega)
  have hrightScheduled := fp2MulScheduledRight_eq_of_low yst out a b hbEnd hbLow
    houtHigh (by omega)
  refine {
    evaluated := step_fp2Mul yst out a b
    output_canonical := fp2MulFinalState_canonical_of_low yst out a b
      ha hb haEnd haLow hbEnd hbLow houtHigh hout
    output_toField_mulSource := ?_
    output_toLawful_mul := fp2MulFinalState_toLawful_mul_of_low yst out a b
      ha hb haEnd haLow hbEnd hbLow houtHigh hout
    lowMemory_preserved := ?_ }
  · calc
      Fp2.toField (fp2At (fp2MulFinalState yst out a b) out) =
          Fp2.toField (fp2MulLeftInput yst a b) *
            Fp2.toField (fp2MulRightInput yst a b) :=
        fp2MulFinalState_toField_mul yst out a b
          (hleftInput.symm ▸ ha) (hrightInput.symm ▸ hb)
          hleftScheduled hrightScheduled houtHigh hout
      _ = Fp2.toField (fp2At yst a) * Fp2.toField (fp2At yst b) := by
        rw [hleftInput, hrightInput]
      _ = Fp2.toField (Fp2.mulSource (fp2At yst a) (fp2At yst b)) :=
        (Fp2.mulSource_spec ha hb).2.symm
  · intro offset hend
    exact fp2MulFinalState_loadWord_before_scratch yst out a b offset hend
      houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
