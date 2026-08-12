import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorFull
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvCall

set_option warningAsError true

/-! Frozen prefix of the optimizer-inlined inversion on the unequal denominator. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalInvBody : Block Op :=
  match pointAddUnequalInvStmt with
  | .block body => body
  | _ => []

def pointAddUnequalInvStmt0 : Stmt Op := pointAddUnequalInvBody[0]!
def pointAddUnequalInvStmt1 : Stmt Op := pointAddUnequalInvBody[1]!
def pointAddUnequalInvStmt2 : Stmt Op := pointAddUnequalInvBody[2]!
def pointAddUnequalInvStmt3 : Stmt Op := pointAddUnequalInvBody[3]!
def pointAddUnequalInvStmt4 : Stmt Op := pointAddUnequalInvBody[4]!
def pointAddUnequalInvStmt5 : Stmt Op := pointAddUnequalInvBody[5]!
def pointAddUnequalInvStmt6 : Stmt Op := pointAddUnequalInvBody[6]!
def pointAddUnequalInvStmt7 : Stmt Op := pointAddUnequalInvBody[7]!
def pointAddUnequalInvStmt8 : Stmt Op := pointAddUnequalInvBody[8]!
def pointAddUnequalInvStmt9 : Stmt Op := pointAddUnequalInvBody[9]!
def pointAddUnequalInvStmt10 : Stmt Op := pointAddUnequalInvBody[10]!
def pointAddUnequalInvStmt11 : Stmt Op := pointAddUnequalInvBody[11]!
def pointAddUnequalInvStmt12 : Stmt Op := pointAddUnequalInvBody[12]!
def pointAddUnequalInvStmt13 : Stmt Op := pointAddUnequalInvBody[13]!

theorem pointAddUnequalInvStmt_eq : pointAddUnequalInvStmt =
    .block pointAddUnequalInvBody := by rfl

theorem pointAddUnequalInvBody_eq : pointAddUnequalInvBody =
    [pointAddUnequalInvStmt0, pointAddUnequalInvStmt1,
      pointAddUnequalInvStmt2, pointAddUnequalInvStmt3,
      pointAddUnequalInvStmt4, pointAddUnequalInvStmt5,
      pointAddUnequalInvStmt6, pointAddUnequalInvStmt7,
      pointAddUnequalInvStmt8, pointAddUnequalInvStmt9,
      pointAddUnequalInvStmt10, pointAddUnequalInvStmt11,
      pointAddUnequalInvStmt12, pointAddUnequalInvStmt13] := by rfl

theorem hoist_pointAddUnequalInvBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddUnequalInvBody = [] := by
  rfl

theorem pointAddUnequalInvStmt9_eq : pointAddUnequalInvStmt9 =
    .cond
      (.builtin .iszero
        [.builtin .staticcall
          [.lit (.number 36576), .lit (.number 5), .lit (.number 1024),
            .lit (.number 240), .lit (.number 1280), .lit (.number 48)]])
      [.exprStmt (.builtin .invalid [])] := by rfl

theorem pointAddUnequalInvStmt1_eq : pointAddUnequalInvStmt1 =
    .block
      [.letDecl ["fc2_9"] (some (.var "\x00131")),
       .block
        [.letDecl ["fc2_10"] (some (.var "\x00130")),
         .exprStmt (.builtin .mstore
          [.lit (.number 1024), .lit (.number 48)]),
         .exprStmt (.builtin .mstore
          [.lit (.number 1056), .lit (.number 48)]),
         .exprStmt (.builtin .mstore
          [.lit (.number 1088), .lit (.number 48)]),
         .letDecl [] none,
         .exprStmt (.builtin .mstore
          [.lit (.number 1120),
           .builtin .shl [.lit (.number 128), .var "fc2_10"]])],
       .exprStmt (.builtin .mstore
        [.lit (.number 1136), .var "fc2_9"])] := by
  rfl

def pointAddUnequalInvGenericEnv (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00132", 0), ("\x00133", 0), ("\x00130", hi), ("\x00131", lo)] ++ tail

def pointAddUnequalInvGenericWorkEnv
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect) (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc2_7", 0), ("fc2_8", 0)] ++
    pointAddUnequalInvGenericEnv tail hi lo

@[simp] private theorem restore_cons_self (V : VEnv D)
    (name : Ident) (value : D.Value) :
    restore V ((name, value) :: V) = V := by
  apply restore_append_of_length_eq (outer := V)
    (locals := [(name, value)]) (inner := V)
  rfl

@[simp] private theorem restore_self (V : VEnv D) : restore V V = V := by
  apply restore_append_of_length_eq (outer := V) (locals := []) (inner := V)
  rfl

def pointAddUnequalInvMstoreState (yst : EvmState)
    (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with
    memory := storeWord yst.memory offset value }

def pointAddUnequalInvHeaderState (yst : EvmState) : EvmState :=
  pointAddUnequalInvMstoreState
    (pointAddUnequalInvMstoreState
      (pointAddUnequalInvMstoreState yst 1024 48) 1056 48) 1088 48

def pointAddUnequalInvBaseState (yst : EvmState) (hi lo : U256) : EvmState :=
  pointAddUnequalInvMstoreState
    (pointAddUnequalInvMstoreState (pointAddUnequalInvHeaderState yst)
      1120 (hi <<< 128)) 1136 lo

def pointAddUnequalInvInputStateGeneric (yst : EvmState)
    (hi lo : U256) : EvmState :=
  pointAddUnequalInvMstoreState
    (pointAddUnequalInvMstoreState
      (pointAddUnequalInvMstoreState
        (pointAddUnequalInvMstoreState (pointAddUnequalInvBaseState yst hi lo)
          1168 (BitVec.ofNat 256
            11762024554600535993938308040068522739871412259351471353901582648940435603456))
        1184 (BitVec.ofNat 256
          45442060874369865957053122457065728162598490762543039060009208264153100167849))
      1216 (BitVec.ofNat 256
        11762024554600535993938308040068522739871412259351471353901582648940435603456))
    1232 (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167851)

theorem exec_pointAddUnequalInvVarsGeneric
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns)
      (pointAddUnequalInvGenericEnv tail hi lo) yst
      pointAddUnequalInvStmt0 =
    .ok (pointAddUnequalInvGenericWorkEnv tail hi lo, yst, .normal) := by
  rfl

theorem exec_pointAddUnequalInvFixedGeneric
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns)
      (pointAddUnequalInvGenericWorkEnv tail hi lo)
      (pointAddUnequalInvBaseState yst hi lo)
      [pointAddUnequalInvStmt2, pointAddUnequalInvStmt3,
        pointAddUnequalInvStmt4, pointAddUnequalInvStmt5,
        pointAddUnequalInvStmt6, pointAddUnequalInvStmt7,
        pointAddUnequalInvStmt8] =
    .ok (pointAddUnequalInvGenericWorkEnv tail hi lo,
      pointAddUnequalInvInputStateGeneric yst hi lo, .normal) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
