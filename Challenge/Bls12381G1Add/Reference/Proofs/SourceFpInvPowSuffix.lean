import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowHighLow

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowDecodedEnv (aHi aLo : U256) (base acc decoded : MontResultValue) :
    VEnv D :=
  VEnv.setMany (fpPowAccEnv aHi aLo base acc) ["\x00126", "\x00125"]
    [decoded.lo, decoded.hi]

theorem fpPowStmt5_shape : fpPowStmt5 =
    .assign ["\x00126", "\x00125"] (.call "\x0015"
      [.var "\x00129", .var "\x00130", .lit (.number 1), .lit (.number 0)]) := by
  rfl

theorem step_fpPowSuffix (aHi aLo : U256) (base acc : MontResultValue)
    (yst : EvmState) :
    ∃ decoded,
      ExecStmt D fpPowBodyFuns (fpPowAccEnv aHi aLo base acc) yst fpPowStmt5
        (fpPowDecodedEnv aHi aLo base acc decoded) yst .normal ∧
      NativeMontMulResult acc.lo acc.hi 1 0 decoded.lo decoded.hi := by
  have hargs : EvalArgs D fpPowBodyFuns (fpPowAccEnv aHi aLo base acc) yst
      [.var "\x00129", .var "\x00130", .lit (.number 1), .lit (.number 0)]
      (.vals [acc.lo, acc.hi, 1, 0] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      Step.lit) Step.lit) (Step.var (by rfl))) (Step.var (by rfl))
  obtain ⟨decodedLo, decodedHi, hcall, hdecodedNative⟩ :=
    step_montMul2_nativeResult
      (callerFuns := fpPowBodyFuns) (V := fpPowAccEnv aHi aLo base acc)
      (args := [.var "\x00129", .var "\x00130",
        .lit (.number 1), .lit (.number 0)])
      (yst := yst) acc.lo acc.hi 1 0 lookup_montMul2_fpPowBody hargs
  let decoded : MontResultValue := { lo := decodedLo, hi := decodedHi }
  refine ⟨decoded, ?_, hdecodedNative⟩
  rw [fpPowStmt5_shape]
  exact Step.assignVal hcall rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
