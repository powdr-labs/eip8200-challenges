import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGeDefs

set_option warningAsError true

/-! Frozen statements and environments for staged G1MSM `fpAdd`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def fpAddStmt0 : Stmt Op :=
  .assign ["\x0039"] (.builtin .add [.var "\x0035", .var "\x0037"])

def fpAddStmt1 : Stmt Op :=
  .assign ["\x0038"]
    (.builtin .add
      [.var "\x0034",
       .builtin .add
        [.var "\x0036",
         .builtin .lt [.var "\x0039", .var "\x0035"]]])

def fpAddStmt2 : Stmt Op :=
  .cond (.call "\x000" [.var "\x0038", .var "\x0039"])
    [.letDecl ["\x0042"]
      (some (.builtin .sub
        [.var "\x0039",
         .lit (.number
           45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
     .assign ["\x0038"]
      (.builtin .sub
        [.var "\x0038",
         .builtin .add
          [.lit (.number 34565483545414906068789196026815425751),
           .builtin .gt
            [.lit (.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851),
             .var "\x0039"]]]),
     .assign ["\x0039"] (.var "\x0042")]

def fpAddBody : Block Op := [fpAddStmt0, fpAddStmt1, fpAddStmt2]

theorem hoist_fpAddBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fpAddBody = [] := by
  rfl

def fpAddBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def fpAddDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0034", "\x0035", "\x0036", "\x0037"]
    rets := ["\x0038", "\x0039"]
    body := fpAddBody }

theorem lookup_fpAdd : lookupFun sourceFuns "\x004" =
    some (fpAddDecl, sourceFuns) := by
  rfl

def fpAddInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0034", ahi), ("\x0035", alo), ("\x0036", bhi), ("\x0037", blo),
   ("\x0038", 0), ("\x0039", 0)]

def fpAddLowValue (alo blo : U256) : U256 := alo + blo

def fpAddLowEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0034", ahi), ("\x0035", alo), ("\x0036", bhi), ("\x0037", blo),
   ("\x0038", 0), ("\x0039", fpAddLowValue alo blo)]

def fpAddHighValue (ahi alo bhi blo : U256) : U256 :=
  ahi + (bhi + b2w (BitVec.ult (fpAddLowValue alo blo) alo))

def fpAddHighEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0034", ahi), ("\x0035", alo), ("\x0036", bhi), ("\x0037", blo),
   ("\x0038", fpAddHighValue ahi alo bhi blo),
   ("\x0039", fpAddLowValue alo blo)]

def fpAddCorrectLowValue (alo blo : U256) : U256 :=
  fpAddLowValue alo blo - BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851

def fpAddCorrectHighValue (ahi alo bhi blo : U256) : U256 :=
  fpAddHighValue ahi alo bhi blo -
    (BitVec.ofNat 256 34565483545414906068789196026815425751 +
      b2w (BitVec.ult (fpAddLowValue alo blo)
        (BitVec.ofNat 256
          45442060874369865957053122457065728162598490762543039060009208264153100167851)))

def fpAddCorrectEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0034", ahi), ("\x0035", alo), ("\x0036", bhi), ("\x0037", blo),
   ("\x0038", fpAddCorrectHighValue ahi alo bhi blo),
   ("\x0039", fpAddCorrectLowValue alo blo)]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
