import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulLawful
set_option warningAsError true
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
#check step_fp2Mul

example (yst : YulSemantics.EVM.EvmState)
    (out a b : YulSemantics.EVM.U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst a))
    (hb : Challenge.Bls12381.ProofSupport.Fp2.Canonical (fp2At yst b))
    (haEnd : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024)
    (hbEnd : b.toNat + 96 < 2 ^ 256) (hbLow : b.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    Fp2MulLowContract yst out a b :=
  fp2Mul_low_contract yst out a b ha hb haEnd haLow hbEnd hbLow
    houtHigh hout

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2Mul_low_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fp2Mul_low_contract
/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.step_fp2Mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_fp2Mul
