import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorFull

set_option warningAsError true

/-! Value-only boundary for the unequal denominator `right.x - left.x`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDenominatorRawBody : Block Op :=
  match pointAddUnequalDenominatorRawStmt with
  | .block body => body
  | _ => []

def pointAddUnequalDenominatorRawStmt0 : Stmt Op :=
  pointAddUnequalDenominatorRawBody[0]!
def pointAddUnequalDenominatorRawStmt1 : Stmt Op :=
  pointAddUnequalDenominatorRawBody[1]!
def pointAddUnequalDenominatorRawStmt2 : Stmt Op :=
  pointAddUnequalDenominatorRawBody[2]!
def pointAddUnequalDenominatorRawStmt3 : Stmt Op :=
  pointAddUnequalDenominatorRawBody[3]!
def pointAddUnequalDenominatorRawStmt4 : Stmt Op :=
  pointAddUnequalDenominatorRawBody[4]!
def pointAddUnequalDenominatorRawStmt5 : Stmt Op :=
  pointAddUnequalDenominatorRawBody[5]!

theorem pointAddUnequalDenominatorDeclStmt_eq :
    pointAddUnequalDenominatorDeclStmt = .letDecl ["fc0_74", "fc0_75"] none := by
  rfl

theorem pointAddUnequalDenominatorRawStmt_eq :
    pointAddUnequalDenominatorRawStmt =
      .block pointAddUnequalDenominatorRawBody := by rfl

theorem pointAddUnequalDenominatorRawBody_eq :
    pointAddUnequalDenominatorRawBody =
      [pointAddUnequalDenominatorRawStmt0, pointAddUnequalDenominatorRawStmt1,
       pointAddUnequalDenominatorRawStmt2, pointAddUnequalDenominatorRawStmt3,
       pointAddUnequalDenominatorRawStmt4,
       pointAddUnequalDenominatorRawStmt5] := by rfl

theorem pointAddUnequalDenominatorRawStmt0_eq :
    pointAddUnequalDenominatorRawStmt0 =
      .letDecl ["fc0_76"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])) := by
  rfl

theorem pointAddUnequalDenominatorRawStmt1_eq :
    pointAddUnequalDenominatorRawStmt1 =
      .letDecl ["fc0_77"]
        (some (.builtin .mload [.builtin .mload [.lit (.number 1568)]])) := by
  rfl

theorem pointAddUnequalDenominatorRawStmt2_eq :
    pointAddUnequalDenominatorRawStmt2 =
      .letDecl ["fc0_78"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]])) := by
  rfl

theorem pointAddUnequalDenominatorRawStmt3_eq :
    pointAddUnequalDenominatorRawStmt3 =
      .letDecl ["fc0_79"]
        (some (.builtin .mload [.builtin .mload [.lit (.number 1600)]])) := by
  rfl

theorem pointAddUnequalDenominatorRawStmt4_eq :
    pointAddUnequalDenominatorRawStmt4 =
      .assign ["fc0_75"]
        (.builtin .sub [.var "fc0_78", .var "fc0_76"]) := by rfl

theorem pointAddUnequalDenominatorRawStmt5_eq :
    pointAddUnequalDenominatorRawStmt5 =
      .assign ["fc0_74"]
        (.builtin .sub
          [.builtin .sub [.var "fc0_79", .var "fc0_77"],
           .builtin .gt [.var "fc0_76", .var "fc0_78"]]) := by rfl

theorem pointAddUnequalDenominatorRepairStmt_eq :
    pointAddUnequalDenominatorRepairStmt =
      .cond
        (.builtin .gt
          [.var "fc0_74",
           .lit (.number 34565483545414906068789196026815425751)])
        [.letDecl ["\x0051"]
          (some (.builtin .add
            [.var "fc0_75",
             .lit (.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
         .assign ["fc0_74"]
          (.builtin .add
            [.var "fc0_74",
             .builtin .add
              [.lit (.number 34565483545414906068789196026815425751),
               .builtin .lt [.var "\x0051", .var "fc0_75"]]]),
         .assign ["fc0_75"] (.var "\x0051")] := by rfl

theorem pointAddUnequalDenominatorOutHiStmt_eq :
    pointAddUnequalDenominatorOutHiStmt =
      .assign ["\x00130"] (.var "fc0_74") := by rfl

theorem pointAddUnequalDenominatorOutLoStmt_eq :
    pointAddUnequalDenominatorOutLoStmt =
      .assign ["\x00131"] (.var "fc0_75") := by rfl

def pointAddUnequalLeftXHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddUnequalNumeratorInputsState yst out left right).memory
    (pointAddUnequalLeftPtr yst out left right).toNat

def pointAddUnequalLeftXLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddUnequalNumeratorInputsState yst out left right).memory
    (pointAddUnequalLeftPtr yst out left right + 32).toNat

def pointAddUnequalRightXHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddUnequalNumeratorInputsState yst out left right).memory
    (pointAddUnequalRightPtr yst out left right).toNat

def pointAddUnequalRightXLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddUnequalNumeratorInputsState yst out left right).memory
    (pointAddUnequalRightPtr yst out left right + 32).toNat

def pointAddUnequalDenominatorRaw (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  (pointAddUnequalRightXHi yst out left right -
      pointAddUnequalLeftXHi yst out left right -
        b2w (BitVec.ult (pointAddUnequalRightXLo yst out left right)
          (pointAddUnequalLeftXLo yst out left right)),
    pointAddUnequalRightXLo yst out left right -
      pointAddUnequalLeftXLo yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
