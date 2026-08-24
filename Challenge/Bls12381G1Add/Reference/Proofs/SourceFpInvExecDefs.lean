import Challenge.Bls12381G1Add.Reference.Proofs.SourceMulWord
import Challenge.Bls12381.ProofSupport.FpMontgomeryMul
import Challenge.Bls12381.ProofSupport.YulModexp
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Native frozen G1ADD inversion helper definitions -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev E := Challenge.YulProof.ClosedEvm.exec
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpInvFuns : FunEnv D :=
  [hoist D Compilation.referenceCompiledBlock]

def fpInvBody : Block Op :=
  match Compilation.referenceCompiledBlock[10]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpPowPMinus2Body : Block Op :=
  match Compilation.referenceCompiledBlock[13]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def montMul2Body : Block Op :=
  match Compilation.referenceCompiledBlock[15]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def montMul2BodyFuns : FunEnv D := [] :: fpInvFuns

def fpInvDecl : FDecl D :=
  { params := ["\x0080", "\x0081"]
    rets := ["\x0082", "\x0083"]
    body := fpInvBody }

def fpPowPMinus2Decl : FDecl D :=
  { params := ["\x00123", "\x00124"]
    rets := ["\x00125", "\x00126"]
    body := fpPowPMinus2Body }

def montMul2Decl : FDecl D :=
  { params := ["\x00166", "\x00167", "\x00168", "\x00169"]
    rets := ["\x00170", "\x00171"]
    body := montMul2Body }

theorem lookup_fpInv : lookupFun fpInvFuns "\x0010" =
    some (fpInvDecl, fpInvFuns) := by rfl

theorem lookup_fpPowPMinus2 : lookupFun fpInvFuns "\x0013" =
    some (fpPowPMinus2Decl, fpInvFuns) := by rfl

theorem lookup_montMul2 : lookupFun fpInvFuns "\x0015" =
    some (montMul2Decl, fpInvFuns) := by rfl

theorem lookup_fpGe_montMul2Body :
    lookupFun montMul2BodyFuns "\x000" = lookupFun fpInvFuns "\x000" := by
  rfl

structure MontStateValue where
  t0 : U256
  t1 : U256
  t2 : U256

def montAccumulateZeroValue (xLo yLo yHi : U256) : MontStateValue :=
  let p0 := fullWordValue xLo yLo
  let p1 := fullWordValue xLo yHi
  let sum := p1.lo + p0.hi
  { t0 := p0.lo
    t1 := sum
    t2 := p1.hi + b2w (BitVec.ult sum p1.lo) }

def montReduceValue (state : MontStateValue) : MontStateValue :=
  let factor := state.t0 * BitVec.ofNat 256
    0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd
  let low := fullWordValue factor (BitVec.ofNat 256
    0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)
  let sum := state.t0 + low.lo
  let carry := low.hi + b2w (BitVec.ult sum state.t0)
  let high := fullWordValue factor (BitVec.ofNat 256
    0x1a0111ea397fe69a4b1ba7b6434bacd7)
  let highSum := state.t1 + high.lo
  let carry1 := b2w (BitVec.ult highSum state.t1)
  let shifted := highSum + carry
  let carry2 := b2w (BitVec.ult shifted highSum)
  { t0 := shifted
    t1 := state.t2 + (high.hi + (carry1 + carry2))
    t2 := 0 }

def montAccumulateNextValue (state : MontStateValue)
    (xHi yLo yHi : U256) : MontStateValue :=
  let low := fullWordValue xHi yLo
  let lowSum := state.t0 + low.lo
  let carry := low.hi + b2w (BitVec.ult lowSum state.t0)
  let high := fullWordValue xHi yHi
  let highSum := state.t1 + high.lo
  let carry1 := b2w (BitVec.ult highSum state.t1)
  let shifted := highSum + carry
  let carry2 := b2w (BitVec.ult shifted highSum)
  { t0 := lowSum
    t1 := shifted
    t2 := high.hi + (carry1 + carry2) }

structure MontResultValue where
  lo : U256
  hi : U256

def montFinalCorrectValue (result : MontResultValue) : MontResultValue :=
  if fpGeModulusValue result.hi result.lo = 0 then result else
    let pHi := BitVec.ofNat 256 0x1a0111ea397fe69a4b1ba7b6434bacd7
    let pLo := BitVec.ofNat 256
      0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
    let nextLo := result.lo - pLo
    { lo := nextLo
      hi := result.hi - pHi - b2w (BitVec.ult result.lo pLo) }

@[irreducible] def montMul2Value (xLo xHi yLo yHi : U256) : MontResultValue :=
  let first := montReduceValue (montAccumulateZeroValue xLo yLo yHi)
  let second := montReduceValue (montAccumulateNextValue first xHi yLo yHi)
  montFinalCorrectValue { lo := second.t0, hi := second.t1 }

def convMontState (state : MontStateValue) :
    Challenge.Bls12381.ProofSupport.Fp.MontgomeryState :=
  { t0 := YulEvmCompiler.conv state.t0
    t1 := YulEvmCompiler.conv state.t1
    t2 := YulEvmCompiler.conv state.t2 }

def convMontResult (result : MontResultValue) :
    Fp.Limbs :=
  { lo := YulEvmCompiler.conv result.lo
    hi := YulEvmCompiler.conv result.hi }

theorem conv_montAccumulateZeroValue (xLo yLo yHi : U256) :
    convMontState (montAccumulateZeroValue xLo yLo yHi) =
      Fp.montgomeryAccumulateZero (YulEvmCompiler.conv xLo)
        (YulEvmCompiler.conv yLo) (YulEvmCompiler.conv yHi) := by
  rw [Fp.MontgomeryState.mk.injEq]
  simp only [convMontState, montAccumulateZeroValue,
    Fp.montgomeryAccumulateZero, Challenge.EvmProof.Limbs.addTwo256]
  simp only [YulEvmCompiler.conv_add, YulEvmCompiler.conv_lt,
    conv_fullWordValue_hi, conv_fullWordValue_lo]
  simp

theorem conv_montReduceValue (state : MontStateValue) :
    convMontState (montReduceValue state) =
      Fp.montgomeryReduceStep (convMontState state) := by
  rw [Fp.MontgomeryState.mk.injEq]
  simp only [convMontState, montReduceValue, Fp.montgomeryReduceStep,
    Fp.montgomeryReductionShiftedSum, Fp.montgomeryReductionHighSum,
    Fp.montgomeryReductionHighProduct, Fp.montgomeryReductionMultiplier,
    Fp.montgomeryReductionCarry, Fp.montgomeryReductionLowProduct,
    Fp.montgomeryReductionLowSum, Challenge.EvmProof.Limbs.addTwo256]
  simp only [YulEvmCompiler.conv_add, YulEvmCompiler.conv_mul,
    YulEvmCompiler.conv_lt, conv_fullWordValue_hi,
    conv_fullWordValue_lo]
  all_goals try norm_num [YulEvmCompiler.conv_eq_ofNat,
    Fp.montgomeryN0Inv, Fp.modulusLo, Fp.modulusHi]
  rfl

theorem conv_montAccumulateNextValue (state : MontStateValue)
    (xHi yLo yHi : U256) :
    convMontState (montAccumulateNextValue state xHi yLo yHi) =
      Fp.montgomeryAccumulateNext (convMontState state)
        (YulEvmCompiler.conv xHi)
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } := by
  rw [Fp.MontgomeryState.mk.injEq]
  simp only [convMontState, montAccumulateNextValue,
    Fp.montgomeryAccumulateNext, Fp.montgomeryNextShiftedSum,
    Fp.montgomeryNextHighSum, Fp.montgomeryNextHighProduct,
    Fp.montgomeryNextCarry, Fp.montgomeryNextLowSum,
    Fp.montgomeryNextLowProduct, Challenge.EvmProof.Limbs.addTwo256]
  simp only [YulEvmCompiler.conv_add, YulEvmCompiler.conv_lt,
    conv_fullWordValue_hi, conv_fullWordValue_lo]
  simp

private theorem fpGeModulusValue_zero_iff (result : MontResultValue) :
    fpGeModulusValue result.hi result.lo = 0 ↔
      (Fp.addNeedsCorrection (convMontResult result)).toNat = 0 := by
  change fpGeModulusValue result.hi result.lo = 0 ↔
    (Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv result.hi,
        lo := YulEvmCompiler.conv result.lo }).toNat = 0
  constructor
  · intro hzero
    have hconv := conv_fpGeModulusValue result.hi result.lo
    rw [hzero] at hconv
    have hnat := congrArg UInt256.toNat hconv
    rw [YulEvmCompiler.conv_toNat] at hnat
    exact hnat.symm
  · intro hzero
    rw [← YulEvmCompiler.conv_inj, conv_fpGeModulusValue]
    apply Challenge.EvmProof.Word.word_ext
    rw [YulEvmCompiler.conv_toNat, show (0 : U256).toNat = 0 by decide]
    exact hzero

theorem conv_montFinalCorrectValue (result : MontResultValue) :
    convMontResult (montFinalCorrectValue result) =
      Fp.ofWide (Fp.montgomeryFinalCorrect (Fp.toWide (convMontResult result))) := by
  unfold montFinalCorrectValue Fp.montgomeryFinalCorrect
  rw [← Fp.addNeedsCorrection_eq_wideGeWord]
  by_cases hzero : fpGeModulusValue result.hi result.lo = 0
  · rw [if_pos hzero, if_neg]
    · rfl
    · exact fun hne => hne ((fpGeModulusValue_zero_iff result).mp hzero)
  · rw [if_neg hzero, if_pos]
    · simp only [convMontResult, Fp.ofWide, Fp.toWide,
        Fp.montgomeryFinalSubModulus]
      rw [Fp.Limbs.mk.injEq]
      simp only [YulEvmCompiler.conv_sub, YulEvmCompiler.conv_lt]
      norm_num [YulEvmCompiler.conv_eq_ofNat, Fp.modulusHi, Fp.modulusLo]
      simp [UInt256.gt, UInt256.lt]
    · exact fun h => hzero ((fpGeModulusValue_zero_iff result).mpr h)

theorem conv_montMul2Value (xLo xHi yLo yHi : U256) :
    convMontResult (montMul2Value xLo xHi yLo yHi) =
      Fp.montMul2
        { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi }
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } := by
  let first := montReduceValue (montAccumulateZeroValue xLo yLo yHi)
  let second := montReduceValue (montAccumulateNextValue first xHi yLo yHi)
  have hfirst : convMontState first =
      Fp.montgomeryFirstReduce (YulEvmCompiler.conv xLo)
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } := by
    rw [show first = montReduceValue
      (montAccumulateZeroValue xLo yLo yHi) by rfl,
      conv_montReduceValue, conv_montAccumulateZeroValue]
    rfl
  have hacc : convMontState (montAccumulateNextValue first xHi yLo yHi) =
      Fp.montgomerySecondAccumulate
        { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi }
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } := by
    rw [conv_montAccumulateNextValue, hfirst]
    rfl
  have hsecond : convMontState second =
      Fp.montgomerySecondReduce
        { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi }
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } := by
    rw [show second = montReduceValue
      (montAccumulateNextValue first xHi yLo yHi) by rfl,
      conv_montReduceValue, hacc]
    rfl
  unfold montMul2Value
  change convMontResult (montFinalCorrectValue { lo := second.t0, hi := second.t1 }) = _
  rw [conv_montFinalCorrectValue]
  unfold Fp.montMul2 Fp.montMul2Words Fp.montgomeryResultWords
  have hwords : Fp.toWide (convMontResult { lo := second.t0, hi := second.t1 }) =
      { lo := (Fp.montgomerySecondReduce
          { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi }
          { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }).t0,
        hi := (Fp.montgomerySecondReduce
          { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi }
          { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }).t1 } := by
    rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
    exact ⟨congrArg Fp.MontgomeryState.t1 hsecond,
      congrArg Fp.MontgomeryState.t0 hsecond⟩
  rw [hwords]

/-- Opaque arithmetic view of one native source multiplication.  Long source
traces refer to this boundary without elaborating the concrete CIOS word
graph or the reducible shared `Fp.montMul2` definition. -/
@[irreducible] def abstractMontMul2 (xLo xHi yLo yHi : U256) : Fp.Limbs :=
  Fp.montMul2
    { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi }
    { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }

theorem conv_montMul2Value_abstract (xLo xHi yLo yHi : U256) :
    convMontResult (montMul2Value xLo xHi yLo yHi) =
      abstractMontMul2 xLo xHi yLo yHi := by
  unfold abstractMontMul2
  exact conv_montMul2Value xLo xHi yLo yHi

theorem canonical_abstractMontMul2 {xLo xHi yLo yHi : U256}
    (hx : Fp.Canonical
      { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi })
    (hy : Fp.Canonical
      { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }) :
    Fp.Canonical (abstractMontMul2 xLo xHi yLo yHi) := by
  unfold abstractMontMul2
  exact Fp.canonical_montMul2 hx hy

theorem lawful_abstractMontMul2 {xLo xHi yLo yHi : U256}
    (hx : Fp.Canonical
      { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi })
    (hy : Fp.Canonical
      { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }) :
    (Fp.value (abstractMontMul2 xLo xHi yLo yHi) : PrimeField.LawfulFp) =
      (Fp.value
        { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi } :
          PrimeField.LawfulFp) *
      (Fp.value
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } :
          PrimeField.LawfulFp) *
      (Fp.montgomeryRadix : PrimeField.LawfulFp)⁻¹ := by
  unfold abstractMontMul2
  exact Fp.lawful_montMul2 hx hy

theorem canonical_conv_montMul2Value {xLo xHi yLo yHi : U256}
    (hx : Fp.Canonical
      { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi })
    (hy : Fp.Canonical
      { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }) :
    Fp.Canonical (convMontResult (montMul2Value xLo xHi yLo yHi)) := by
  rw [conv_montMul2Value_abstract]
  exact canonical_abstractMontMul2 hx hy

theorem lawful_conv_montMul2Value {xLo xHi yLo yHi : U256}
    (hx : Fp.Canonical
      { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi })
    (hy : Fp.Canonical
      { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi }) :
    (Fp.value (convMontResult (montMul2Value xLo xHi yLo yHi)) :
        PrimeField.LawfulFp) =
      (Fp.value
        { lo := YulEvmCompiler.conv xLo, hi := YulEvmCompiler.conv xHi } :
          PrimeField.LawfulFp) *
      (Fp.value
        { lo := YulEvmCompiler.conv yLo, hi := YulEvmCompiler.conv yHi } :
          PrimeField.LawfulFp) *
      (Fp.montgomeryRadix : PrimeField.LawfulFp)⁻¹ := by
  rw [conv_montMul2Value_abstract]
  exact lawful_abstractMontMul2 hx hy

def montMul2Stmt0 : Stmt Op := montMul2Body[0]!
def montMul2Stmt1 : Stmt Op := montMul2Body[1]!
def montMul2Stmt2 : Stmt Op := montMul2Body[2]!
def montMul2Stmt3 : Stmt Op := montMul2Body[3]!
def montMul2Stmt4 : Stmt Op := montMul2Body[4]!
def montMul2Stmt5 : Stmt Op := montMul2Body[5]!
def montMul2Stmt6 : Stmt Op := montMul2Body[6]!
def montMul2Stmt7 : Stmt Op := montMul2Body[7]!
def montMul2Stmt8 : Stmt Op := montMul2Body[8]!
def montMul2Stmt9 : Stmt Op := montMul2Body[9]!

theorem montMul2Body_eq : montMul2Body =
    [montMul2Stmt0, montMul2Stmt1, montMul2Stmt2, montMul2Stmt3,
      montMul2Stmt4, montMul2Stmt5, montMul2Stmt6, montMul2Stmt7,
      montMul2Stmt8, montMul2Stmt9] := by rfl

def montMul2InitialEnv (xLo xHi yLo yHi : U256) : VEnv D :=
  [("\x00166", xLo), ("\x00167", xHi), ("\x00168", yLo),
    ("\x00169", yHi), ("\x00170", 0), ("\x00171", 0)]

def montMul2StateEnv (outer : VEnv D) (state : MontStateValue) : VEnv D :=
  [("\x00174", state.t2), ("\x00173", state.t1), ("\x00172", state.t0)] ++ outer

def montMul2FactorValue (state : MontStateValue) : U256 :=
  state.t0 * BitVec.ofNat 256
    0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd

def montMul2WorkEnv (outer : VEnv D) (factor : U256)
    (state : MontStateValue) : VEnv D :=
  [("\x00180", factor)] ++
    montMul2StateEnv outer state

def montMul2FactorEnv (outer : VEnv D) (state : MontStateValue) : VEnv D :=
  montMul2WorkEnv outer (montMul2FactorValue state) state

def montMul2OutputEnv (outer : VEnv D) (workState output : MontStateValue) :
    VEnv D :=
  VEnv.setMany (montMul2FactorEnv outer workState) ["\x00170", "\x00171"]
    [output.t0, output.t1]

/- Named stages keep the relational source proof small.  They are irreducible
outside the individual straight-line certificates, so later loop proofs carry
compact terms instead of repeatedly normalizing the complete CIOS graph. -/
@[irreducible] def montInitial (xLo yLo yHi : U256) : MontStateValue :=
  montAccumulateZeroValue xLo yLo yHi

@[irreducible] def montFirst (xLo yLo yHi : U256) : MontStateValue :=
  montReduceValue (montInitial xLo yLo yHi)

@[irreducible] def montAccumulated (xLo xHi yLo yHi : U256) : MontStateValue :=
  montAccumulateNextValue (montFirst xLo yLo yHi) xHi yLo yHi

@[irreducible] def montSecond (xLo xHi yLo yHi : U256) : MontStateValue :=
  montReduceValue (montAccumulated xLo xHi yLo yHi)

theorem montMul2Value_eq_stages (xLo xHi yLo yHi : U256) :
    montMul2Value xLo xHi yLo yHi = montFinalCorrectValue
      { lo := (montSecond xLo xHi yLo yHi).t0,
        hi := (montSecond xLo xHi yLo yHi).t1 } := by
  simp only [montMul2Value, montSecond, montAccumulated, montFirst, montInitial]

def montMul2FinalEnv (xLo xHi yLo yHi : U256) : VEnv D :=
  VEnv.setMany
    (montMul2OutputEnv (montMul2InitialEnv xLo xHi yLo yHi)
      (montAccumulated xLo xHi yLo yHi) (montSecond xLo xHi yLo yHi))
    ["\x00170", "\x00171"]
    [(montMul2Value xLo xHi yLo yHi).lo,
      (montMul2Value xLo xHi yLo yHi).hi]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
