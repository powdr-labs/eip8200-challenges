import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvEnv

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def loopFuns : FunEnv D := [] :: fpPowBodyFuns
def loopBodyFuns : FunEnv D := [] :: loopFuns
def loopCondFuns : FunEnv D := [] :: loopBodyFuns

theorem lookup_mont_loopBody :
    lookupFun loopBodyFuns "\x0015" = some (montMul2Decl, fpInvFuns) := by rfl
theorem lookup_mont_loopCond :
    lookupFun loopCondFuns "\x0015" = some (montMul2Decl, fpInvFuns) := by rfl

def setBit (V : VEnv D) (name : Ident) (bit : Nat) : VEnv D :=
  VEnv.set V name (BitVec.ofNat 256 bit)

def setAcc (V : VEnv D) (acc : MontResultValue) : VEnv D :=
  VEnv.set (VEnv.set V "\x00129" acc.lo) "\x00130" acc.hi

structure PowLoopInv (V : VEnv D) (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) : Prop where
  bit : VEnv.get V bitName = some (BitVec.ofNat 256 bit)
  accLo : VEnv.get V "\x00129" = some acc.lo
  accHi : VEnv.get V "\x00130" = some acc.hi
  baseLo : VEnv.get V "\x00127" = some base.lo
  baseHi : VEnv.get V "\x00128" = some base.hi

/-- The loop-local countdown variable is the sole binding introduced by the
`for` initializer.  Keeping this small scoping fact separate from the value
invariant makes restoration at the end of the source `for` compositional. -/
def PowLoopHead (V : VEnv D) (bitName : Ident) (bit : Nat) : Prop :=
  ∃ tail : VEnv D, V = (bitName, BitVec.ofNat 256 bit) :: tail

theorem PowLoopHead.afterSetBit {V : VEnv D} {bitName : Ident} {bit : Nat}
    (hhead : PowLoopHead V bitName bit) (next : Nat) :
    PowLoopHead (setBit V bitName next) bitName next := by
  rcases hhead with ⟨tail, rfl⟩
  exact ⟨tail, by simp [setBit, VEnv.set]⟩

theorem PowLoopHead.afterSetAcc {V : VEnv D} {bitName : Ident} {bit : Nat}
    (hhead : PowLoopHead V bitName bit) (next : MontResultValue)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130") :
    PowLoopHead (setAcc V next) bitName bit := by
  rcases hhead with ⟨tail, rfl⟩
  exact ⟨setAcc tail next, by
    simp [setAcc, VEnv.set, hfreshLo, hfreshHi]⟩

theorem set_length {D : Dialect} (V : VEnv D) (name : Ident) (value : D.Value) :
    (VEnv.set V name value).length = V.length := by
  induction V with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨other, current⟩
      simp only [VEnv.set]
      split <;> simp [ih]

theorem setAcc_length (V : VEnv D) (acc : MontResultValue) :
    (setAcc V acc).length = V.length := by
  rw [setAcc, set_length, set_length]

theorem setBit_length (V : VEnv D) (name : Ident) (bit : Nat) :
    (setBit V name bit).length = V.length := by
  rw [setBit, set_length]

theorem restore_of_length_eq {D : Dialect} (outer inner : VEnv D)
    (hlen : inner.length = outer.length) : restore outer inner = inner := by
  simp [restore, hlen]

theorem PowLoopInv.afterSetBit {V : VEnv D} {bitName : Ident} {bit : Nat}
    {base acc : MontResultValue} (hinv : PowLoopInv V bitName bit base acc)
    (next : Nat)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130")
    (hfreshBaseLo : bitName ≠ "\x00127")
    (hfreshBaseHi : bitName ≠ "\x00128") :
    PowLoopInv (setBit V bitName next) bitName next base acc := by
  constructor
  · exact vget_set_self V bitName _ _ hinv.bit
  · rw [setBit, vget_set_other V bitName "\x00129" _ hfreshLo]
    exact hinv.accLo
  · rw [setBit, vget_set_other V bitName "\x00130" _ hfreshHi]
    exact hinv.accHi
  · rw [setBit, vget_set_other V bitName "\x00127" _ hfreshBaseLo]
    exact hinv.baseLo
  · rw [setBit, vget_set_other V bitName "\x00128" _ hfreshBaseHi]
    exact hinv.baseHi

theorem PowLoopInv.afterSetAcc {V : VEnv D} {bitName : Ident} {bit : Nat}
    {base acc : MontResultValue} (hinv : PowLoopInv V bitName bit base acc)
    (next : MontResultValue)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130") :
    PowLoopInv (setAcc V next) bitName bit base next := by
  constructor
  · rw [setAcc, vget_set_other _ "\x00130" bitName _ (Ne.symm hfreshHi),
      vget_set_other _ "\x00129" bitName _ (Ne.symm hfreshLo)]
    exact hinv.bit
  · rw [setAcc, vget_set_other _ "\x00130" "\x00129" _ (by decide)]
    exact vget_set_self V "\x00129" _ _ hinv.accLo
  · apply vget_set_self
    rw [vget_set_other V "\x00129" "\x00130" _ (by decide)]
    exact hinv.accHi
  · rw [setAcc, vget_set_other _ "\x00130" "\x00127" _ (by decide),
      vget_set_other _ "\x00129" "\x00127" _ (by decide)]
    exact hinv.baseLo
  · rw [setAcc, vget_set_other _ "\x00130" "\x00128" _ (by decide),
      vget_set_other _ "\x00129" "\x00128" _ (by decide)]
    exact hinv.baseHi

def loopStepEnv (V : VEnv D) (bitName : Ident) (base acc : MontResultValue)
    (word : U256) (bit : Nat) : VEnv D :=
  let decremented := setBit V bitName bit
  let squared := montMul2Value acc.lo acc.hi acc.lo acc.hi
  let squaredEnv := setAcc decremented squared
  if sourceWordBit word bit = 0 then squaredEnv
  else setAcc squaredEnv (montMul2Value squared.lo squared.hi base.lo base.hi)

theorem loopStepEnv_length (V : VEnv D) (bitName : Ident)
    (base acc : MontResultValue) (word : U256) (bit : Nat) :
    (loopStepEnv V bitName base acc word bit).length = V.length := by
  unfold loopStepEnv
  split
  · rw [setAcc_length, setBit_length]
  · rw [setAcc_length, setAcc_length, setBit_length]

theorem PowLoopInv.afterLoopStep {V : VEnv D} {bitName : Ident} {bit : Nat}
    {base acc : MontResultValue} (hinv : PowLoopInv V bitName (bit + 1) base acc)
    (word : U256)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130")
    (hfreshBaseLo : bitName ≠ "\x00127")
    (hfreshBaseHi : bitName ≠ "\x00128") :
    PowLoopInv (loopStepEnv V bitName base acc word bit) bitName bit base
      (montBitStepValue base acc word bit) := by
  have hdec := hinv.afterSetBit bit hfreshLo hfreshHi hfreshBaseLo hfreshBaseHi
  let squared := montMul2Value acc.lo acc.hi acc.lo acc.hi
  have hsq : PowLoopInv (setAcc (setBit V bitName bit) squared)
      bitName bit base squared := hdec.afterSetAcc squared hfreshLo hfreshHi
  unfold loopStepEnv montBitStepValue
  by_cases hzero : sourceWordBit word bit = 0
  · rw [if_pos hzero, if_pos hzero]
    exact hsq
  · rw [if_neg hzero, if_neg hzero]
    exact hsq.afterSetAcc
      (montMul2Value squared.lo squared.hi base.lo base.hi) hfreshLo hfreshHi

@[irreducible] def loopRunEnv (bitName : Ident) (base : MontResultValue) (word : U256) :
    Nat → VEnv D → MontResultValue → VEnv D
  | 0, V, _ => V
  | bit + 1, V, acc =>
      loopRunEnv bitName base word bit (loopStepEnv V bitName base acc word bit)
        (montBitStepValue base acc word bit)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
