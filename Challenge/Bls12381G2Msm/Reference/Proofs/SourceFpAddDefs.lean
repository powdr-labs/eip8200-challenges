import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpCore

set_option warningAsError true

/-! Frozen statements and environments for staged G2MSM `fpAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def fpAddStmt0 : Stmt Op :=
  .assign ["\x0052"] (.builtin .add [.var "\x0048", .var "\x0050"])

def fpAddStmt1 : Stmt Op :=
  .assign ["\x0051"]
    (.builtin .add
      [.builtin .add [.var "\x0047", .var "\x0049"],
       .builtin .lt [.var "\x0052", .var "\x0048"]])

def fpAddStmt2 : Stmt Op :=
  .cond (.call "\x000" [.var "\x0051", .var "\x0052"])
    [.letDecl ["\x0053"]
      (some (.lit (.number 34565483545414906068789196026815425751))),
     .letDecl ["\x0054"]
      (some (.lit (.number
        45442060874369865957053122457065728162598490762543039060009208264153100167851))),
     .letDecl ["\x0055"]
      (some (.builtin .sub [.var "\x0052", .var "\x0054"])),
     .assign ["\x0051"]
      (.builtin .sub
        [.var "\x0051",
         .builtin .add
          [.var "\x0053", .builtin .gt [.var "\x0054", .var "\x0052"]]]),
     .assign ["\x0052"] (.var "\x0055")]

def fpAddBody : Block Op := [fpAddStmt0, fpAddStmt1, fpAddStmt2]

def fpAddFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect referenceCompiledBlock]

def fpAddBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fpAddFuns

def fpAddDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0047", "\x0048", "\x0049", "\x0050"]
    rets := ["\x0051", "\x0052"]
    body := fpAddBody }

theorem lookup_fpAdd : lookupFun fpAddFuns "\x004" =
    some (fpAddDecl, fpAddFuns) := by
  rfl

def fpAddInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0047", ahi), ("\x0048", alo), ("\x0049", bhi), ("\x0050", blo),
   ("\x0051", 0), ("\x0052", 0)]

def fpAddLowValue (alo blo : U256) : U256 := alo + blo

def fpAddLowEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpAddInitialEnv ahi alo bhi blo) ["\x0052"]
    [fpAddLowValue alo blo]

def fpAddHighValue (ahi alo bhi blo : U256) : U256 :=
  ahi + bhi + b2w (BitVec.ult (fpAddLowValue alo blo) alo)

def fpAddHighEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpAddLowEnv ahi alo bhi blo) ["\x0051"]
    [fpAddHighValue ahi alo bhi blo]

def fpAddCorrectLowValue (alo blo : U256) : U256 :=
  fpAddLowValue alo blo - fpModulusLoValue

def fpAddCorrectHighValue (ahi alo bhi blo : U256) : U256 :=
  fpAddHighValue ahi alo bhi blo -
    (fpModulusHiValue + b2w (BitVec.ult (fpAddLowValue alo blo)
      fpModulusLoValue))

def fpAddCorrectEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  let env := fpAddHighEnv ahi alo bhi blo
  let nextLo := fpAddCorrectLowValue alo blo
  let nextHi := fpAddCorrectHighValue ahi alo bhi blo
  VEnv.setMany env ["\x0051", "\x0052"] [nextHi, nextLo]

def fpAddFinalEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  let env := fpAddHighEnv ahi alo bhi blo
  if fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) = (0#256) then env else
    fpAddCorrectEnv ahi alo bhi blo

def fpAddResult (ahi alo bhi blo : U256) : U256 × U256 :=
  let final := fpAddFinalEnv ahi alo bhi blo
  ((VEnv.get final "\x0051").getD (0#256),
   (VEnv.get final "\x0052").getD (0#256))

theorem fpAddFinalEnv_length (ahi alo bhi blo : U256) :
    (fpAddFinalEnv ahi alo bhi blo).length = 6 := by
  unfold fpAddFinalEnv
  split <;> rfl

theorem restore_fpAddFinalEnv (ahi alo bhi blo : U256) :
    restore (fpAddInitialEnv ahi alo bhi blo)
      (fpAddFinalEnv ahi alo bhi blo) = fpAddFinalEnv ahi alo bhi blo := by
  unfold restore
  rw [fpAddFinalEnv_length]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
