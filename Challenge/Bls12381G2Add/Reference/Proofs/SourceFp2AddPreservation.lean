import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddInputs

set_option warningAsError true

/-! # Memory preservation below a frozen G2ADD `fp2Add` output -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem fp2AddFinalState_loadWord_before_out
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    loadWord (fp2AddFinalState yst out a b).memory offset =
      loadWord yst.memory offset := by
  unfold fp2AddFinalState fp2AddAfterC1High
  change loadWord
    (storeWord (storeWord (fp2AddAfterC1Reads yst out a b).memory
      (out + BitVec.ofNat 256 64).toNat _)
      (out + BitVec.ofNat 256 96).toNat _) offset = _
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by right; bv_omega)]
  have hreads : (fp2AddAfterC1Reads yst out a b).memory =
      (fp2AddAfterC0Stores yst out a b).memory := rfl
  rw [hreads]
  unfold fp2AddAfterC0Stores fp2AddAfterC0High
  change loadWord (storeWord (storeWord yst.memory out.toNat _)
    (out + BitVec.ofNat 256 32).toNat _) offset = _
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by right; bv_omega)]

theorem fp2AddFinalState_fp2At_before_out
    (yst : EvmState) (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hbefore : ptr.toNat + 128 ≤ out.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2AddFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    exact fp2AddFinalState_loadWord_before_out yst out a b _
      (by bv_omega) houtEnd

/-- The proof-facing effect of one `fp2Add` call.  The exact seven-state
execution graph is deliberately absent: callers receive the source execution,
the selected output value, and a frame fact for memory below the output. -/
structure Fp2AddRunContract (yst : EvmState) (out a b : U256)
    (final : EvmState) : Prop where
  execution :
    Interp.evalExpr Challenge.EvmProof.modexpExec 72 fp2AddFuns
      [("out", out), ("a", a), ("b", b)] yst
      (.call "\x0014" [.var "out", .var "a", .var "b"]) =
        .ok (.vals [] final)
  output :
    fp2At final out =
      Challenge.Bls12381.ProofSupport.Fp2.addSource
        (fp2AddScheduledA yst out a b) (fp2AddScheduledB yst out a b)
  loadWord_before_out : ∀ offset : Nat, offset + 32 ≤ out.toNat →
    loadWord final.memory offset = loadWord yst.memory offset

/-- Computable representative of the relational result.  Its private bridge
equation is established before the definition is made irreducible, so later
proofs cannot accidentally unfold the concrete execution graph. -/
def fp2AddContractState (yst : EvmState) (out a b : U256) : EvmState :=
  fp2AddFinalState yst out a b

private theorem fp2AddContractState_eq (yst : EvmState) (out a b : U256) :
    fp2AddContractState yst out a b = fp2AddFinalState yst out a b := by
  rfl

theorem eval_fp2AddContractState (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 72 fp2AddFuns
      [("out", out), ("a", a), ("b", b)] yst
      (.call "\x0014" [.var "out", .var "a", .var "b"]) =
        .ok (.vals [] (fp2AddContractState yst out a b)) := by
  rw [fp2AddContractState_eq]
  exact eval_fp2Add out a b yst

theorem fp2AddContractState_output (yst : EvmState) (out a b : U256)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2AddContractState yst out a b) out =
      Challenge.Bls12381.ProofSupport.Fp2.addSource
        (fp2AddScheduledA yst out a b) (fp2AddScheduledB yst out a b) := by
  rw [fp2AddContractState_eq,
    fp2AddFinalState_output yst out a b houtEnd,
    fp2AddResult_eq_addSource]

/-- Both inputs are wholly below the output region, so neither is changed by
the scheduled first-component stores. -/
theorem fp2AddContractState_output_inputs_before
    (yst : EvmState) (out a b : U256)
    (houtEnd : out.toNat + 96 < 2 ^ 256)
    (ha : a.toNat + 128 ≤ out.toNat)
    (hb : b.toNat + 128 ≤ out.toNat) :
    fp2At (fp2AddContractState yst out a b) out =
      Challenge.Bls12381.ProofSupport.Fp2.addSource
        (fp2At yst a) (fp2At yst b) := by
  rw [fp2AddContractState_output yst out a b houtEnd,
    fp2AddScheduledA_eq_before_out yst out a b ha (by omega),
    fp2AddScheduledB_eq_before_out yst out a b hb (by omega)]

/-- The left input aliases the output and the right input is wholly below it.
This is the update shape used by the second numerator addition in doubling. -/
theorem fp2AddContractState_output_inplace_left_before
    (yst : EvmState) (out b : U256)
    (houtEnd : out.toNat + 96 < 2 ^ 256)
    (hb : b.toNat + 128 ≤ out.toNat) :
    fp2At (fp2AddContractState yst out out b) out =
      Challenge.Bls12381.ProofSupport.Fp2.addSource
        (fp2At yst out) (fp2At yst b) := by
  rw [fp2AddContractState_output yst out out b houtEnd,
    fp2AddScheduledA_eq_at_out yst out b houtEnd,
    fp2AddScheduledB_eq_before_out yst out out b hb (by omega)]

/-- Common in-place schedule: the left input aliases the output, while the
right input begins after the two first-component output words. -/
theorem fp2AddContractState_output_inplace_right_after
    (yst : EvmState) (out b : U256)
    (houtEnd : out.toNat + 96 < 2 ^ 256)
    (hb : out.toNat + 64 ≤ b.toNat)
    (hbEnd : b.toNat + 96 < 2 ^ 256) :
    fp2At (fp2AddContractState yst out out b) out =
      Challenge.Bls12381.ProofSupport.Fp2.addSource
        (fp2At yst out) (fp2At yst b) := by
  rw [fp2AddContractState_output yst out out b houtEnd,
    fp2AddScheduledA_eq_at_out yst out b houtEnd,
    fp2AddScheduledB_eq_after_out_c0 yst out out b
      (by omega) hb hbEnd]

theorem fp2AddContractState_loadWord_before_out
    (yst : EvmState) (out a b : U256)
    (houtEnd : out.toNat + 96 < 2 ^ 256) (offset : Nat)
    (hend : offset + 32 ≤ out.toNat) :
    loadWord (fp2AddContractState yst out a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2AddContractState_eq]
  exact fp2AddFinalState_loadWord_before_out yst out a b offset hend houtEnd

theorem fp2AddContractState_fp2At_before_out
    (yst : EvmState) (out a b ptr : U256)
    (houtEnd : out.toNat + 96 < 2 ^ 256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hbefore : ptr.toNat + 128 ≤ out.toNat) :
    fp2At (fp2AddContractState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    exact fp2AddContractState_loadWord_before_out yst out a b houtEnd _
      (by bv_omega)

/-- Connect the concrete source evaluator to the relational layer once.  The
exact final state is absent from this theorem's statement. -/
theorem fp2Add_contract_exists (yst : EvmState) (out a b : U256)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    ∃ final, Fp2AddRunContract yst out a b final := by
  refine ⟨fp2AddContractState yst out a b, ?_⟩
  constructor
  · exact eval_fp2AddContractState yst out a b
  · exact fp2AddContractState_output yst out a b houtEnd
  · intro offset hend
    exact fp2AddContractState_loadWord_before_out
      yst out a b houtEnd offset hend

attribute [irreducible] fp2AddContractState

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
