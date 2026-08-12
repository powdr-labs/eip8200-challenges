import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalEntry

set_option warningAsError true

/-! Value-only boundary for the unequal numerator `right.y - left.y`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalNumeratorRawBody : Block Op :=
  match pointAddUnequalNumeratorRawStmt with
  | .block body => body
  | _ => []

def pointAddUnequalNumeratorRawStmt0 : Stmt Op :=
  pointAddUnequalNumeratorRawBody[0]!
def pointAddUnequalNumeratorRawStmt1 : Stmt Op :=
  pointAddUnequalNumeratorRawBody[1]!
def pointAddUnequalNumeratorRawStmt2 : Stmt Op :=
  pointAddUnequalNumeratorRawBody[2]!
def pointAddUnequalNumeratorRawStmt3 : Stmt Op :=
  pointAddUnequalNumeratorRawBody[3]!
def pointAddUnequalNumeratorRawStmt4 : Stmt Op :=
  pointAddUnequalNumeratorRawBody[4]!
def pointAddUnequalNumeratorRawStmt5 : Stmt Op :=
  pointAddUnequalNumeratorRawBody[5]!

theorem pointAddUnequalNumeratorDeclStmt_eq :
    pointAddUnequalNumeratorDeclStmt = .letDecl ["fc0_67", "fc0_68"] none := by
  rfl

theorem pointAddUnequalNumeratorRawStmt_eq :
    pointAddUnequalNumeratorRawStmt =
      .block pointAddUnequalNumeratorRawBody := by
  rfl

theorem pointAddUnequalNumeratorRawBody_eq :
    pointAddUnequalNumeratorRawBody =
      [pointAddUnequalNumeratorRawStmt0, pointAddUnequalNumeratorRawStmt1,
       pointAddUnequalNumeratorRawStmt2, pointAddUnequalNumeratorRawStmt3,
       pointAddUnequalNumeratorRawStmt4,
       pointAddUnequalNumeratorRawStmt5] := by
  rfl

theorem pointAddUnequalNumeratorRawStmt0_eq :
    pointAddUnequalNumeratorRawStmt0 =
      .letDecl ["fc0_69"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])) := by
  rfl

theorem pointAddUnequalNumeratorRawStmt1_eq :
    pointAddUnequalNumeratorRawStmt1 =
      .letDecl ["fc0_70"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])) := by
  rfl

theorem pointAddUnequalNumeratorRawStmt2_eq :
    pointAddUnequalNumeratorRawStmt2 =
      .letDecl ["fc0_71"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 96)]])) := by
  rfl

theorem pointAddUnequalNumeratorRawStmt3_eq :
    pointAddUnequalNumeratorRawStmt3 =
      .letDecl ["fc0_72"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 64)]])) := by
  rfl

theorem pointAddUnequalNumeratorRawStmt4_eq :
    pointAddUnequalNumeratorRawStmt4 =
      .assign ["fc0_68"]
        (.builtin .sub [.var "fc0_71", .var "fc0_69"]) := by
  rfl

theorem pointAddUnequalNumeratorRawStmt5_eq :
    pointAddUnequalNumeratorRawStmt5 =
      .assign ["fc0_67"]
        (.builtin .sub
          [.builtin .sub [.var "fc0_72", .var "fc0_70"],
           .builtin .gt [.var "fc0_69", .var "fc0_71"]]) := by
  rfl

theorem pointAddUnequalNumeratorRepairStmt_eq :
    pointAddUnequalNumeratorRepairStmt =
      .cond
        (.builtin .gt
          [.var "fc0_67",
           .lit (.number 34565483545414906068789196026815425751)])
        [.letDecl ["\x0051"]
          (some (.builtin .add
            [.var "fc0_68",
             .lit (.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
         .assign ["fc0_67"]
          (.builtin .add
            [.var "fc0_67",
             .builtin .add
              [.lit (.number 34565483545414906068789196026815425751),
               .builtin .lt [.var "\x0051", .var "fc0_68"]]]),
         .assign ["fc0_68"] (.var "\x0051")] := by
  rfl

theorem pointAddUnequalNumeratorOutHiStmt_eq :
    pointAddUnequalNumeratorOutHiStmt =
      .assign ["\x00128"] (.var "fc0_67") := by
  rfl

theorem pointAddUnequalNumeratorOutLoStmt_eq :
    pointAddUnequalNumeratorOutLoStmt =
      .assign ["\x00129"] (.var "fc0_68") := by
  rfl

def pointAddUnequalLeftPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddXEqState yst out left right).memory 1568

def pointAddUnequalRightPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddXEqState yst out left right).memory 1600

def pointAddUnequalLeftYHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddXEqState yst out left right).memory
    (pointAddUnequalLeftPtr yst out left right + 64).toNat

def pointAddUnequalLeftYLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddXEqState yst out left right).memory
    (pointAddUnequalLeftPtr yst out left right + 96).toNat

def pointAddUnequalRightYHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddXEqState yst out left right).memory
    (pointAddUnequalRightPtr yst out left right + 64).toNat

def pointAddUnequalRightYLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddXEqState yst out left right).memory
    (pointAddUnequalRightPtr yst out left right + 96).toNat

def pointAddUnequalNumeratorRawLo (yst : EvmState)
    (out left right : U256) : U256 :=
  pointAddUnequalRightYLo yst out left right -
    pointAddUnequalLeftYLo yst out left right

def pointAddUnequalNumeratorBorrow (yst : EvmState)
    (out left right : U256) : U256 :=
  b2w (BitVec.ult (pointAddUnequalRightYLo yst out left right)
    (pointAddUnequalLeftYLo yst out left right))

def pointAddUnequalNumeratorRawHi (yst : EvmState)
    (out left right : U256) : U256 :=
  pointAddUnequalRightYHi yst out left right -
    pointAddUnequalLeftYHi yst out left right -
      pointAddUnequalNumeratorBorrow yst out left right

def pointAddUnequalNumeratorRaw (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  (pointAddUnequalNumeratorRawHi yst out left right,
    pointAddUnequalNumeratorRawLo yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
