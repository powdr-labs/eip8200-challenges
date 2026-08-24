import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvCall

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowStmt0 : Stmt Op := fpPowPMinus2Body[0]!
def fpPowStmt1 : Stmt Op := fpPowPMinus2Body[1]!
def fpPowStmt2 : Stmt Op := fpPowPMinus2Body[2]!
def fpPowStmt3 : Stmt Op := fpPowPMinus2Body[3]!
def fpPowStmt4 : Stmt Op := fpPowPMinus2Body[4]!
def fpPowStmt5 : Stmt Op := fpPowPMinus2Body[5]!

theorem fpPowBody_eq : fpPowPMinus2Body =
    [fpPowStmt0, fpPowStmt1, fpPowStmt2, fpPowStmt3, fpPowStmt4, fpPowStmt5] := by
  rfl

def fpPowBodyFuns : FunEnv D := [] :: fpInvFuns

theorem lookup_montMul2_fpPowBody : lookupFun fpPowBodyFuns "\x0015" =
    some (montMul2Decl, fpInvFuns) := by
  rfl

def fpPowInitialEnv (aHi aLo : U256) : VEnv D :=
  [("\x00123", aHi), ("\x00124", aLo), ("\x00125", 0), ("\x00126", 0)]

@[irreducible] def fpPowBaseValue (aHi aLo : U256) : MontResultValue :=
  montMul2Value aLo aHi
    (BitVec.ofNat 256 92286679234085438351495039074048687640204382693166976402664901553327635873368)
    (BitVec.ofNat 256 86499536527081971458999430873902347)

def fpPowBaseEnv (aHi aLo : U256) : VEnv D :=
  [("\x00127", (fpPowBaseValue aHi aLo).lo),
    ("\x00128", (fpPowBaseValue aHi aLo).hi)] ++ fpPowInitialEnv aHi aLo

def fpPowAccEnv (aHi aLo : U256) (base acc : MontResultValue) : VEnv D :=
  [("\x00130", acc.hi), ("\x00129", acc.lo),
    ("\x00127", base.lo), ("\x00128", base.hi)] ++ fpPowInitialEnv aHi aLo

def sourceWordBit (word : U256) (bit : Nat) : U256 :=
  (word >>> (BitVec.ofNat 256 bit).toNat) &&& 1

@[irreducible] def montBitStepValue (base acc : MontResultValue) (word : U256)
    (bit : Nat) : MontResultValue :=
  let squared := montMul2Value acc.lo acc.hi acc.lo acc.hi
  if sourceWordBit word bit = 0 then squared
  else montMul2Value squared.lo squared.hi base.lo base.hi

@[irreducible] def montFoldDownValue (base : MontResultValue) (word : U256) :
    Nat → MontResultValue → MontResultValue
  | 0, acc => acc
  | bit + 1, acc =>
      montFoldDownValue base word bit (montBitStepValue base acc word bit)

def fpPowLoopEnv (aHi aLo : U256) (base acc : MontResultValue)
    (bitName : Ident) (bit : Nat) : VEnv D :=
  [(bitName, BitVec.ofNat 256 bit)] ++ fpPowAccEnv aHi aLo base acc

def fpPowLoopBody (bitName : Ident) (word : Nat) : Block Op :=
  [.assign [bitName] (.builtin .sub [.var bitName, .lit (.number 1)]),
   .assign ["\x00129", "\x00130"] (.call "\x0015"
      [.var "\x00129", .var "\x00130", .var "\x00129", .var "\x00130"]),
   .cond (.builtin .and
      [.builtin .shr [.var bitName, .lit (.number word)], .lit (.number 1)])
     [.assign ["\x00129", "\x00130"] (.call "\x0015"
       [.var "\x00129", .var "\x00130", .var "\x00127", .var "\x00128"])]]

def fpPowHighWord : U256 :=
  BitVec.ofNat 256 34565483545414906068789196026815425751

def fpPowLowWord : U256 := BitVec.ofNat 256
  45442060874369865957053122457065728162598490762543039060009208264153100167849

@[irreducible] def fpPowAfterHigh (aHi aLo : U256) : MontResultValue :=
  let base := fpPowBaseValue aHi aLo
  montFoldDownValue base fpPowHighWord 124 base

@[irreducible] def fpPowAfterLow (aHi aLo : U256) : MontResultValue :=
  let base := fpPowBaseValue aHi aLo
  montFoldDownValue base fpPowLowWord 256 (fpPowAfterHigh aHi aLo)

@[irreducible] def fpPowResult (aHi aLo : U256) : MontResultValue :=
  let acc := fpPowAfterLow aHi aLo
  montMul2Value acc.lo acc.hi 1 0

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
