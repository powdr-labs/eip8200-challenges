import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointPredicatesRefinement

set_option warningAsError true

/-! # Frozen G2ADD point output helper definitions -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def storeConstState (yst : EvmState) (dest : Nat) (value : U256) :
    EvmState :=
  { touchMemory yst dest 32 with memory := storeWord yst.memory dest value }

private def copyWordState (yst : EvmState) (dest : Nat) (src : U256) :
    EvmState :=
  let read := touchMemory yst src.toNat 32
  { touchMemory read dest 32 with
    memory := storeWord read.memory dest (loadWord yst.memory src.toNat) }

private theorem copyWordState_memory (yst : EvmState) (dest : Nat)
    (src : U256) :
    (copyWordState yst dest src).memory =
      storeWord yst.memory dest (loadWord yst.memory src.toNat) := rfl

def clearPointState (yst : EvmState) : EvmState :=
  let s0 := storeConstState yst 0 0
  let s1 := storeConstState s0 32 0
  let s2 := storeConstState s1 64 0
  let s3 := storeConstState s2 96 0
  let s4 := storeConstState s3 128 0
  let s5 := storeConstState s4 160 0
  let s6 := storeConstState s5 192 0
  storeConstState s6 224 0

def copyPointState0 (yst : EvmState) (point : U256) : EvmState :=
  copyWordState yst 0 point

def copyPointState1 (yst : EvmState) (point : U256) : EvmState :=
  copyWordState (copyPointState0 yst point) 32
    (point + BitVec.ofNat 256 32)

def copyPointState2 (yst : EvmState) (point : U256) : EvmState :=
  copyWordState (copyPointState1 yst point) 64
    (point + BitVec.ofNat 256 64)

def copyPointState3 (yst : EvmState) (point : U256) : EvmState :=
  copyWordState (copyPointState2 yst point) 96
    (point + BitVec.ofNat 256 96)

def copyPointState4 (yst : EvmState) (point : U256) : EvmState :=
  copyWordState (copyPointState3 yst point) 128
    (point + BitVec.ofNat 256 128)

def copyPointState5 (yst : EvmState) (point : U256) : EvmState :=
  copyWordState (copyPointState4 yst point) 160
    (point + BitVec.ofNat 256 160)

def copyPointState6 (yst : EvmState) (point : U256) : EvmState :=
  copyWordState (copyPointState5 yst point) 192
    (point + BitVec.ofNat 256 192)

def copyPointState (yst : EvmState) (point : U256) : EvmState :=
  copyWordState (copyPointState6 yst point) 224
    (point + BitVec.ofNat 256 224)

theorem copyPointState0_memory (yst : EvmState) (point : U256) :
    (copyPointState0 yst point).memory =
      storeWord yst.memory 0 (loadWord yst.memory point.toNat) := by rfl

theorem copyPointState1_memory (yst : EvmState) (point : U256) :
    (copyPointState1 yst point).memory =
      storeWord (copyPointState0 yst point).memory 32
        (loadWord (copyPointState0 yst point).memory
          (point + BitVec.ofNat 256 32).toNat) := by rfl

theorem copyPointState2_memory (yst : EvmState) (point : U256) :
    (copyPointState2 yst point).memory =
      storeWord (copyPointState1 yst point).memory 64
        (loadWord (copyPointState1 yst point).memory
          (point + BitVec.ofNat 256 64).toNat) := by rfl

theorem copyPointState3_memory (yst : EvmState) (point : U256) :
    (copyPointState3 yst point).memory =
      storeWord (copyPointState2 yst point).memory 96
        (loadWord (copyPointState2 yst point).memory
          (point + BitVec.ofNat 256 96).toNat) := by rfl

theorem copyPointState4_memory (yst : EvmState) (point : U256) :
    (copyPointState4 yst point).memory =
      storeWord (copyPointState3 yst point).memory 128
        (loadWord (copyPointState3 yst point).memory
          (point + BitVec.ofNat 256 128).toNat) := by rfl

theorem copyPointState5_memory (yst : EvmState) (point : U256) :
    (copyPointState5 yst point).memory =
      storeWord (copyPointState4 yst point).memory 160
        (loadWord (copyPointState4 yst point).memory
          (point + BitVec.ofNat 256 160).toNat) := by rfl

theorem copyPointState6_memory (yst : EvmState) (point : U256) :
    (copyPointState6 yst point).memory =
      storeWord (copyPointState5 yst point).memory 192
        (loadWord (copyPointState5 yst point).memory
          (point + BitVec.ofNat 256 192).toNat) := by rfl

theorem copyPointState_memory (yst : EvmState) (point : U256) :
    (copyPointState yst point).memory =
      storeWord (copyPointState6 yst point).memory 224
        (loadWord (copyPointState6 yst point).memory
          (point + BitVec.ofNat 256 224).toNat) := by rfl

def storePointState (yst : EvmState) (x y : U256) : EvmState :=
  let s0 := copyWordState yst 0 x
  let s1 := copyWordState s0 32 (x + BitVec.ofNat 256 32)
  let s2 := copyWordState s1 64 (x + BitVec.ofNat 256 64)
  let s3 := copyWordState s2 96 (x + BitVec.ofNat 256 96)
  let s4 := copyWordState s3 128 y
  let s5 := copyWordState s4 160 (y + BitVec.ofNat 256 32)
  let s6 := copyWordState s5 192 (y + BitVec.ofNat 256 64)
  copyWordState s6 224 (y + BitVec.ofNat 256 96)

/-- At the fixed postlude scratch addresses, the eight point copies read the
original high-memory words.  This shallow memory boundary keeps output-codec
proofs from unfolding the nested source helper. -/
theorem storePointState_memory_2688_2944 (yst : EvmState) :
    (storePointState yst 2688 2944).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 0 (loadWord yst.memory 2688))
                    32 (loadWord yst.memory 2720))
                  64 (loadWord yst.memory 2752))
                96 (loadWord yst.memory 2784))
              128 (loadWord yst.memory 2944))
            160 (loadWord yst.memory 2976))
        192 (loadWord yst.memory 3008))
        224 (loadWord yst.memory 3040) := by
  have hx0 : ((2688 : U256).toNat) = 2688 := by decide
  have hx1 : (2688 + BitVec.ofNat 256 32 : U256).toNat = 2720 := by decide
  have hx2 : (2688 + BitVec.ofNat 256 64 : U256).toNat = 2752 := by decide
  have hx3 : (2688 + BitVec.ofNat 256 96 : U256).toNat = 2784 := by decide
  have hy0 : ((2944 : U256).toNat) = 2944 := by decide
  have hy1 : (2944 + BitVec.ofNat 256 32 : U256).toNat = 2976 := by decide
  have hy2 : (2944 + BitVec.ofNat 256 64 : U256).toNat = 3008 := by decide
  have hy3 : (2944 + BitVec.ofNat 256 96 : U256).toNat = 3040 := by decide
  simp only [storePointState, copyWordState_memory]
  rw [hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  repeat' rw [loadWord_storeWord_disjoint _ _ _ _ (by omega)]

def clearPointBody : Block Op :=
  match Compilation.referenceCompiledBlock[22]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def clearPointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := [], rets := [], body := clearPointBody }

theorem lookup_clearPoint : lookupFun fp2Funs "\x0022" =
    some (clearPointDecl, fp2Funs) := by rfl

def copyPointBody : Block Op :=
  match Compilation.referenceCompiledBlock[23]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def copyPointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00128"], rets := [], body := copyPointBody }

theorem lookup_copyPoint : lookupFun fp2Funs "\x0023" =
    some (copyPointDecl, fp2Funs) := by rfl

def storePointBody : Block Op :=
  match Compilation.referenceCompiledBlock[24]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def storePointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00129", "\x00130"], rets := [], body := storePointBody }

theorem lookup_storePoint : lookupFun fp2Funs "\x0024" =
    some (storePointDecl, fp2Funs) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
