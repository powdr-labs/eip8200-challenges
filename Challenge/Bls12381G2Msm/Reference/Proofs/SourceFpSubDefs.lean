import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpCore

set_option warningAsError true

/-! Frozen statements and environments for staged G2MSM `fpSub`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def fpSubStmt0 : Stmt Op :=
  .assign ["\x0061"] (.builtin .sub [.var "\x0057", .var "\x0059"])

def fpSubStmt1 : Stmt Op :=
  .assign ["\x0060"]
    (.builtin .sub
      [.builtin .sub [.var "\x0056", .var "\x0058"],
       .builtin .gt [.var "\x0059", .var "\x0057"]])

def fpSubStmt2 : Stmt Op :=
  .letDecl ["\x0062"]
    (some (.lit (.number 34565483545414906068789196026815425751)))

def fpSubStmt3 : Stmt Op :=
  .cond (.builtin .gt [.var "\x0060", .var "\x0062"])
    [.letDecl ["\x0063"]
      (some (.lit (.number
        45442060874369865957053122457065728162598490762543039060009208264153100167851))),
     .letDecl ["\x0064"]
      (some (.builtin .add [.var "\x0061", .var "\x0063"])),
     .assign ["\x0060"]
      (.builtin .add
        [.builtin .add [.var "\x0060", .var "\x0062"],
         .builtin .lt [.var "\x0064", .var "\x0061"]]),
     .assign ["\x0061"] (.var "\x0064")]

def fpSubBody : Block Op := [fpSubStmt0, fpSubStmt1, fpSubStmt2, fpSubStmt3]

def fpSubFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect referenceCompiledBlock]

def fpSubBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fpSubFuns

def fpSubDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0056", "\x0057", "\x0058", "\x0059"]
    rets := ["\x0060", "\x0061"]
    body := fpSubBody }

theorem lookup_fpSub : lookupFun fpSubFuns "\x005" =
    some (fpSubDecl, fpSubFuns) := by
  rfl

def fpSubInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0056", ahi), ("\x0057", alo), ("\x0058", bhi), ("\x0059", blo),
   ("\x0060", 0), ("\x0061", 0)]

def fpSubRawLowValue (alo blo : U256) : U256 := alo - blo

def fpSubLowEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpSubInitialEnv ahi alo bhi blo) ["\x0061"]
    [fpSubRawLowValue alo blo]

def fpSubRawHighValue (ahi alo bhi blo : U256) : U256 :=
  ahi - bhi - b2w (BitVec.ult alo blo)

def fpSubRawEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpSubLowEnv ahi alo bhi blo) ["\x0060"]
    [fpSubRawHighValue ahi alo bhi blo]

def fpSubPreBranchEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("\x0062", fpModulusHiValue) :: fpSubRawEnv ahi alo bhi blo

def fpSubRepairedLowValue (alo blo : U256) : U256 :=
  fpSubRawLowValue alo blo + fpModulusLoValue

def fpSubRepairedHighValue (ahi alo bhi blo : U256) : U256 :=
  fpSubRawHighValue ahi alo bhi blo + fpModulusHiValue +
    b2w (BitVec.ult (fpSubRepairedLowValue alo blo) (fpSubRawLowValue alo blo))

def fpSubRepairedEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpSubPreBranchEnv ahi alo bhi blo) ["\x0060", "\x0061"]
    [fpSubRepairedHighValue ahi alo bhi blo, fpSubRepairedLowValue alo blo]

def fpSubBodyFinalEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  if BitVec.ult fpModulusHiValue (fpSubRawHighValue ahi alo bhi blo) then
    fpSubRepairedEnv ahi alo bhi blo
  else fpSubPreBranchEnv ahi alo bhi blo

def fpSubFinalEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fpSubInitialEnv ahi alo bhi blo)
    (fpSubBodyFinalEnv ahi alo bhi blo)

def fpSubResult (ahi alo bhi blo : U256) : U256 × U256 :=
  let final := fpSubFinalEnv ahi alo bhi blo
  ((VEnv.get final "\x0060").getD (0#256),
   (VEnv.get final "\x0061").getD (0#256))

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
