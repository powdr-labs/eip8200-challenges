import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2PredicatesRefinement

set_option warningAsError true

/-!
# Frozen G2ADD `fp2Add` boundary

This module freezes the six source statements and names their exact memory
graph.  In particular, the second component is read after the first component
has been stored.  That distinction preserves the source program's behaviour
even for aliased pointers, without exposing the evaluator to later proofs.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fp2AddFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def fp2AddBody : Block Op :=
  match Compilation.referenceCompiledBlock[14]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2AddStmt0 : Stmt Op := fp2AddBody[0]!
def fp2AddStmt1 : Stmt Op := fp2AddBody[1]!
def fp2AddStmt2 : Stmt Op := fp2AddBody[2]!
def fp2AddStmt3 : Stmt Op := fp2AddBody[3]!
def fp2AddStmt4 : Stmt Op := fp2AddBody[4]!
def fp2AddStmt5 : Stmt Op := fp2AddBody[5]!

theorem fp2AddBody_eq : fp2AddBody =
    [fp2AddStmt0, fp2AddStmt1, fp2AddStmt2,
      fp2AddStmt3, fp2AddStmt4, fp2AddStmt5] := by
  rfl

theorem hoist_fp2AddBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2AddBody = [] := by
  rfl

def fp2AddBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fp2AddFuns

theorem fp2AddBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2AddBody :: fp2AddFuns =
      fp2AddBodyFuns := by
  rw [hoist_fp2AddBody]
  rfl

def fp2AddDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00100", "\x00101", "\x00102"]
    rets := []
    body := fp2AddBody }

theorem lookup_fp2Add : lookupFun fp2AddFuns "\x0014" =
    some (fp2AddDecl, fp2AddFuns) := by
  rfl

def fp2AddInitialEnv (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00100", out), ("\x00101", a), ("\x00102", b)]

private def mstoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

/-- Four scalar limbs loaded for a call to `fpAdd`.  The source interpreter
evaluates call arguments from right to left. -/
def fp2AddReadState (yst : EvmState)
    (ahi alo bhi blo : U256) : EvmState :=
  let s0 := touchMemory yst blo.toNat 32
  let s1 := touchMemory s0 bhi.toNat 32
  let s2 := touchMemory s1 alo.toNat 32
  touchMemory s2 ahi.toNat 32

theorem fp2AddReadState_memory (yst : EvmState) (ahi alo bhi blo : U256) :
    (fp2AddReadState yst ahi alo bhi blo).memory = yst.memory := by
  rfl

/-- The first Fp component is read from the incoming state. -/
def fp2AddC0 (yst : EvmState) (a b : U256) : U256 × U256 :=
  fpAddValue
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory b.toNat)
    (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)

def fp2AddAfterC0Reads (yst : EvmState) (a b : U256) : EvmState :=
  fp2AddReadState yst a (a + BitVec.ofNat 256 32)
    b (b + BitVec.ofNat 256 32)

def fp2AddAfterC0High (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2AddAfterC0Reads yst a b) out (fp2AddC0 yst a b).1

def fp2AddAfterC0Stores (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2AddAfterC0High yst out a b)
    (out + BitVec.ofNat 256 32) (fp2AddC0 yst a b).2

/-- The second Fp component is intentionally read after the first component's
stores, so this graph remains exact for arbitrary pointer aliasing. -/
def fp2AddC1 (yst : EvmState) (out a b : U256) : U256 × U256 :=
  let s := fp2AddAfterC0Stores yst out a b
  fpAddValue
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 96).toNat)

def fp2AddAfterC1Reads (yst : EvmState) (out a b : U256) : EvmState :=
  fp2AddReadState (fp2AddAfterC0Stores yst out a b)
    (a + BitVec.ofNat 256 64) (a + BitVec.ofNat 256 96)
    (b + BitVec.ofNat 256 64) (b + BitVec.ofNat 256 96)

def fp2AddAfterC1High (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2AddAfterC1Reads yst out a b)
    (out + BitVec.ofNat 256 64) (fp2AddC1 yst out a b).1

def fp2AddFinalState (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2AddAfterC1High yst out a b)
    (out + BitVec.ofNat 256 96) (fp2AddC1 yst out a b).2

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
