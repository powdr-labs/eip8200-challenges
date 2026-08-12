import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleLawful

set_option warningAsError true

/-! Frozen statement boundaries for the unequal-x G1MSM `pointAdd` path. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalCode : Block Op := pointAddBody.drop 6

def pointAddUnequalNumeratorInitStmt : Stmt Op := pointAddBody[6]!
def pointAddUnequalNumeratorStmt : Stmt Op := pointAddBody[7]!
def pointAddUnequalDenominatorInitStmt : Stmt Op := pointAddBody[8]!
def pointAddUnequalDenominatorStmt : Stmt Op := pointAddBody[9]!
def pointAddUnequalInvInitStmt : Stmt Op := pointAddBody[10]!
def pointAddUnequalInvStmt : Stmt Op := pointAddBody[11]!
def pointAddUnequalLambdaStmt : Stmt Op := pointAddBody[12]!
def pointAddUnequalX3Stmt : Stmt Op := pointAddBody[13]!
def pointAddUnequalXSubStmt : Stmt Op := pointAddBody[14]!
def pointAddUnequalDeltaInitStmt : Stmt Op := pointAddBody[15]!
def pointAddUnequalDeltaStmt : Stmt Op := pointAddBody[16]!
def pointAddUnequalYMulStmt : Stmt Op := pointAddBody[17]!
def pointAddUnequalYSubStmt : Stmt Op := pointAddBody[18]!
def pointAddUnequalPostInitStmt : Stmt Op := pointAddBody[19]!
def pointAddUnequalPostYLoStmt : Stmt Op := pointAddBody[20]!
def pointAddUnequalPostYHiStmt : Stmt Op := pointAddBody[21]!
def pointAddUnequalPostPtrStmt : Stmt Op := pointAddBody[22]!
def pointAddUnequalStoreXHiStmt : Stmt Op := pointAddBody[23]!
def pointAddUnequalStoreXLoStmt : Stmt Op := pointAddBody[24]!
def pointAddUnequalStoreYHiStmt : Stmt Op := pointAddBody[25]!
def pointAddUnequalStoreYLoStmt : Stmt Op := pointAddBody[26]!

theorem pointAddUnequalCode_eq : pointAddUnequalCode =
    [pointAddUnequalNumeratorInitStmt, pointAddUnequalNumeratorStmt,
     pointAddUnequalDenominatorInitStmt, pointAddUnequalDenominatorStmt,
     pointAddUnequalInvInitStmt, pointAddUnequalInvStmt,
     pointAddUnequalLambdaStmt, pointAddUnequalX3Stmt,
     pointAddUnequalXSubStmt, pointAddUnequalDeltaInitStmt,
     pointAddUnequalDeltaStmt, pointAddUnequalYMulStmt,
     pointAddUnequalYSubStmt, pointAddUnequalPostInitStmt,
     pointAddUnequalPostYLoStmt, pointAddUnequalPostYHiStmt,
     pointAddUnequalPostPtrStmt, pointAddUnequalStoreXHiStmt,
     pointAddUnequalStoreXLoStmt, pointAddUnequalStoreYHiStmt,
     pointAddUnequalStoreYLoStmt] := by
  rfl

def pointAddUnequalNumeratorBody : Block Op :=
  match pointAddUnequalNumeratorStmt with
  | .block body => body
  | _ => []

def pointAddUnequalNumeratorDeclStmt : Stmt Op :=
  pointAddUnequalNumeratorBody[0]!
def pointAddUnequalNumeratorRawStmt : Stmt Op :=
  pointAddUnequalNumeratorBody[1]!
def pointAddUnequalNumeratorRepairStmt : Stmt Op :=
  pointAddUnequalNumeratorBody[2]!
def pointAddUnequalNumeratorOutHiStmt : Stmt Op :=
  pointAddUnequalNumeratorBody[3]!
def pointAddUnequalNumeratorOutLoStmt : Stmt Op :=
  pointAddUnequalNumeratorBody[4]!

theorem pointAddUnequalNumeratorStmt_eq : pointAddUnequalNumeratorStmt =
    .block pointAddUnequalNumeratorBody := by
  rfl

theorem pointAddUnequalNumeratorBody_eq : pointAddUnequalNumeratorBody =
    [pointAddUnequalNumeratorDeclStmt, pointAddUnequalNumeratorRawStmt,
     pointAddUnequalNumeratorRepairStmt, pointAddUnequalNumeratorOutHiStmt,
     pointAddUnequalNumeratorOutLoStmt] := by
  rfl

def pointAddUnequalDenominatorBody : Block Op :=
  match pointAddUnequalDenominatorStmt with
  | .block body => body
  | _ => []

def pointAddUnequalDenominatorDeclStmt : Stmt Op :=
  pointAddUnequalDenominatorBody[0]!
def pointAddUnequalDenominatorRawStmt : Stmt Op :=
  pointAddUnequalDenominatorBody[1]!
def pointAddUnequalDenominatorRepairStmt : Stmt Op :=
  pointAddUnequalDenominatorBody[2]!
def pointAddUnequalDenominatorOutHiStmt : Stmt Op :=
  pointAddUnequalDenominatorBody[3]!
def pointAddUnequalDenominatorOutLoStmt : Stmt Op :=
  pointAddUnequalDenominatorBody[4]!

theorem pointAddUnequalDenominatorStmt_eq : pointAddUnequalDenominatorStmt =
    .block pointAddUnequalDenominatorBody := by
  rfl

theorem pointAddUnequalDenominatorBody_eq : pointAddUnequalDenominatorBody =
    [pointAddUnequalDenominatorDeclStmt, pointAddUnequalDenominatorRawStmt,
     pointAddUnequalDenominatorRepairStmt, pointAddUnequalDenominatorOutHiStmt,
     pointAddUnequalDenominatorOutLoStmt] := by
  rfl

theorem pointAddUnequalNumeratorInitStmt_eq :
    pointAddUnequalNumeratorInitStmt = .letDecl ["\x00128", "\x00129"] none := by
  rfl

theorem pointAddUnequalDenominatorInitStmt_eq :
    pointAddUnequalDenominatorInitStmt = .letDecl ["\x00130", "\x00131"] none := by
  rfl

theorem pointAddUnequalInvInitStmt_eq :
    pointAddUnequalInvInitStmt = .letDecl ["\x00132", "\x00133"] none := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
