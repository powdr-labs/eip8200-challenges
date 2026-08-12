import Challenge.Bls12381G2Msm.Reference.Proofs.SourceOnCurveExec
import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointStores

set_option warningAsError true

/-! Exact arbitrary-address point storage and infinity helpers for G2MSM. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def storeWordState (yst : EvmState) (dest : U256) (value : U256) :
    EvmState :=
  { touchMemory yst dest.toNat 32 with
    memory := storeWord yst.memory dest.toNat value }

private def copyWordState (yst : EvmState) (dest src : U256) : EvmState :=
  let read := touchMemory yst src.toNat 32
  storeWordState read dest (loadWord yst.memory src.toNat)

private theorem copyWordState_memory (yst : EvmState) (dest src : U256) :
    (copyWordState yst dest src).memory =
      storeWord yst.memory dest.toNat (loadWord yst.memory src.toNat) := by
  rfl

def msmStorePointState (yst : EvmState) (ptr x y : U256) : EvmState :=
  let s0 := copyWordState yst ptr x
  let s1 := copyWordState s0 (ptr + 32) (x + 32)
  let s2 := copyWordState s1 (ptr + 64) (x + 64)
  let s3 := copyWordState s2 (ptr + 96) (x + 96)
  let s4 := copyWordState s3 (ptr + 128) y
  let s5 := copyWordState s4 (ptr + 160) (y + 32)
  let s6 := copyWordState s5 (ptr + 192) (y + 64)
  copyWordState s6 (ptr + 224) (y + 96)

/-- At the concrete G2MSM accumulator/scratch addresses, the helper copies
the original eight coordinate words into the accumulator cell. -/
theorem msmStorePointState_memory_3840_2688_2944 (yst : EvmState) :
    (msmStorePointState yst 3840 2688 2944).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 3840 (loadWord yst.memory 2688))
                      3872 (loadWord yst.memory 2720))
                    3904 (loadWord yst.memory 2752))
                  3936 (loadWord yst.memory 2784))
                3968 (loadWord yst.memory 2944))
              4000 (loadWord yst.memory 2976))
            4032 (loadWord yst.memory 3008))
          4064 (loadWord yst.memory 3040) := by
  have hd0 : ((3840 : U256).toNat) = 3840 := by decide
  have hd1 : ((3872 : U256).toNat) = 3872 := by decide
  have hd2 : ((3904 : U256).toNat) = 3904 := by decide
  have hd3 : ((3936 : U256).toNat) = 3936 := by decide
  have hd4 : ((3968 : U256).toNat) = 3968 := by decide
  have hd5 : ((4000 : U256).toNat) = 4000 := by decide
  have hd6 : ((4032 : U256).toNat) = 4032 := by decide
  have hd7 : ((4064 : U256).toNat) = 4064 := by decide
  have hs0 : ((2688 : U256).toNat) = 2688 := by decide
  have hs1 : ((2720 : U256).toNat) = 2720 := by decide
  have hs2 : ((2752 : U256).toNat) = 2752 := by decide
  have hs3 : ((2784 : U256).toNat) = 2784 := by decide
  have hs4 : ((2944 : U256).toNat) = 2944 := by decide
  have hs5 : ((2976 : U256).toNat) = 2976 := by decide
  have hs6 : ((3008 : U256).toNat) = 3008 := by decide
  have hs7 : ((3040 : U256).toNat) = 3040 := by decide
  simp only [msmStorePointState, copyWordState_memory]
  norm_num
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  repeat' rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.loadWord_storeWord_disjoint
    _ _ _ _ (by omega)]

def msmStoreInfinityState (yst : EvmState) (ptr : U256) : EvmState :=
  let s0 := storeWordState yst ptr 0
  let s1 := storeWordState s0 (ptr + 32) 0
  let s2 := storeWordState s1 (ptr + 64) 0
  let s3 := storeWordState s2 (ptr + 96) 0
  let s4 := storeWordState s3 (ptr + 128) 0
  let s5 := storeWordState s4 (ptr + 160) 0
  let s6 := storeWordState s5 (ptr + 192) 0
  storeWordState s6 (ptr + 224) 0

/-- Memory projection of the infinity helper.  This small boundary lets
lawful readback proofs reason about eight stores without reopening the source
evaluator or the active-memory bookkeeping. -/
theorem msmStoreInfinityState_memory (yst : EvmState) (ptr : U256) :
    (msmStoreInfinityState yst ptr).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory ptr.toNat 0)
                      (ptr + 32).toNat 0)
                    (ptr + 64).toNat 0)
                  (ptr + 96).toNat 0)
                (ptr + 128).toNat 0)
              (ptr + 160).toNat 0)
            (ptr + 192).toNat 0)
          (ptr + 224).toNat 0 := by
  rfl

def msmCopyPointState (yst : EvmState) (dst src : U256) : EvmState :=
  let s0 := copyWordState yst dst src
  let s1 := copyWordState s0 (dst + 32) (src + 32)
  let s2 := copyWordState s1 (dst + 64) (src + 64)
  let s3 := copyWordState s2 (dst + 96) (src + 96)
  let s4 := copyWordState s3 (dst + 128) (src + 128)
  let s5 := copyWordState s4 (dst + 160) (src + 160)
  let s6 := copyWordState s5 (dst + 192) (src + 192)
  copyWordState s6 (dst + 224) (src + 224)

def msmStorePointBody : Block Op :=
  match Compilation.referenceCompiledBlock[25]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def msmStorePointPrefix : Block Op := msmStorePointBody.take 4
def msmStorePointTail : Block Op := msmStorePointBody.drop 4

theorem msmStorePointBody_eq : msmStorePointBody =
    msmStorePointPrefix ++ msmStorePointTail := by rfl

def msmStorePointMidState (yst : EvmState) (ptr x : U256) : EvmState :=
  let s0 := copyWordState yst ptr x
  let s1 := copyWordState s0 (ptr + 32) (x + 32)
  let s2 := copyWordState s1 (ptr + 64) (x + 64)
  copyWordState s2 (ptr + 96) (x + 96)

def msmStorePointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00137", "\x00138", "\x00139"]
    rets := []
    body := msmStorePointBody }

theorem lookup_msmStorePoint : lookupFun fp2Funs "\x0025" =
    some (msmStorePointDecl, fp2Funs) := by rfl

def msmStoreInfinityBody : Block Op :=
  match Compilation.referenceCompiledBlock[26]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def msmStoreInfinityPrefix : Block Op := msmStoreInfinityBody.take 4
def msmStoreInfinityTail : Block Op := msmStoreInfinityBody.drop 4

theorem msmStoreInfinityBody_eq : msmStoreInfinityBody =
    msmStoreInfinityPrefix ++ msmStoreInfinityTail := by rfl

def msmStoreInfinityMidState (yst : EvmState) (ptr : U256) : EvmState :=
  let s0 := storeWordState yst ptr 0
  let s1 := storeWordState s0 (ptr + 32) 0
  let s2 := storeWordState s1 (ptr + 64) 0
  storeWordState s2 (ptr + 96) 0

def msmStoreInfinityDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00140"]
    rets := []
    body := msmStoreInfinityBody }

theorem lookup_msmStoreInfinity : lookupFun fp2Funs "\x0026" =
    some (msmStoreInfinityDecl, fp2Funs) := by rfl

def msmCopyPointBody : Block Op :=
  match Compilation.referenceCompiledBlock[27]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def msmCopyPointPrefix : Block Op := msmCopyPointBody.take 4
def msmCopyPointTail : Block Op := msmCopyPointBody.drop 4

theorem msmCopyPointBody_eq : msmCopyPointBody =
    msmCopyPointPrefix ++ msmCopyPointTail := by rfl

def msmCopyPointMidState (yst : EvmState) (dst src : U256) : EvmState :=
  let s0 := copyWordState yst dst src
  let s1 := copyWordState s0 (dst + 32) (src + 32)
  let s2 := copyWordState s1 (dst + 64) (src + 64)
  copyWordState s2 (dst + 96) (src + 96)

def msmCopyPointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00141", "\x00142"]
    rets := []
    body := msmCopyPointBody }

theorem lookup_msmCopyPoint : lookupFun fp2Funs "\x0027" =
    some (msmCopyPointDecl, fp2Funs) := by rfl

def pointInfinityBody : Block Op :=
  match Compilation.referenceCompiledBlock[28]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointInfinityDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00143"]
    rets := ["\x00144"]
    body := pointInfinityBody }

theorem lookup_pointInfinity : lookupFun fp2Funs "\x0028" =
    some (pointInfinityDecl, fp2Funs) := by rfl

private theorem exec_msmStorePointBody (ptr x y : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fp2Funs
      [("\x00137", ptr), ("\x00138", x), ("\x00139", y)] yst
      (.block msmStorePointBody) =
    .ok ([("\x00137", ptr), ("\x00138", x), ("\x00139", y)],
      msmStorePointState yst ptr x y, .normal) := by
  let V := [("\x00137", ptr), ("\x00138", x), ("\x00139", y)]
  have hpre : Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst msmStorePointPrefix =
      .ok (V, msmStorePointMidState yst ptr x, .normal) := by rfl
  have htail : Interp.execStmts Challenge.EvmProof.modexpExec 62
      ([] :: fp2Funs) V (msmStorePointMidState yst ptr x)
      msmStorePointTail =
      .ok (V, msmStorePointState yst ptr x y, .normal) := by rfl
  have hbody := Interp.execStmts_append_normal
    (E := Challenge.EvmProof.modexpExec) (n := 62)
    (pre := msmStorePointPrefix) (tail := msmStorePointTail)
    (by omega) hpre htail
  have hlen : msmStorePointPrefix.length = 4 := by rfl
  rw [hlen] at hbody
  rw [Interp.execStmt, msmStorePointBody_eq]
  rw [show hoist Challenge.EvmProof.modexpExec.toDialect
    (msmStorePointPrefix ++ msmStorePointTail) = [] by rfl]
  change (do
    let result ← Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst (msmStorePointPrefix ++ msmStorePointTail)
    .ok (restore V result.1, result.2.1, result.2.2)) = _
  rw [hbody]
  rfl

theorem eval_msmStorePoint (ptr x y : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("ptr", ptr), ("x", x), ("y", y)] yst
      (.call "\x0025" [.var "ptr", .var "x", .var "y"]) =
    .ok (.vals [] (msmStorePointState yst ptr x y)) := by
  have hcall := Interp.evalExpr_call_normal
    (E := Challenge.EvmProof.modexpExec) (n := 67)
    (V := [("ptr", ptr), ("x", x), ("y", y)]) (st := yst)
    (args := [.var "ptr", .var "x", .var "y"])
    (argvals := [ptr, x, y]) (fn := "\x0025")
    (decl := msmStorePointDecl) (cenv := fp2Funs)
    (Vend := [("\x00137", ptr), ("\x00138", x), ("\x00139", y)])
    (st2 := msmStorePointState yst ptr x y)
    (by rfl) lookup_msmStorePoint (by rfl)
    (exec_msmStorePointBody ptr x y yst)
  simpa [msmStorePointDecl] using hcall

private theorem exec_msmStoreInfinityBody (ptr : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fp2Funs
      [("\x00140", ptr)] yst (.block msmStoreInfinityBody) =
    .ok ([("\x00140", ptr)], msmStoreInfinityState yst ptr, .normal) := by
  let V := [("\x00140", ptr)]
  have hpre : Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst msmStoreInfinityPrefix =
      .ok (V, msmStoreInfinityMidState yst ptr, .normal) := by rfl
  have htail : Interp.execStmts Challenge.EvmProof.modexpExec 62
      ([] :: fp2Funs) V (msmStoreInfinityMidState yst ptr)
      msmStoreInfinityTail =
      .ok (V, msmStoreInfinityState yst ptr, .normal) := by rfl
  have hbody := Interp.execStmts_append_normal
    (E := Challenge.EvmProof.modexpExec) (n := 62)
    (pre := msmStoreInfinityPrefix) (tail := msmStoreInfinityTail)
    (by omega) hpre htail
  have hlen : msmStoreInfinityPrefix.length = 4 := by rfl
  rw [hlen] at hbody
  rw [Interp.execStmt, msmStoreInfinityBody_eq]
  rw [show hoist Challenge.EvmProof.modexpExec.toDialect
    (msmStoreInfinityPrefix ++ msmStoreInfinityTail) = [] by rfl]
  change (do
    let result ← Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst (msmStoreInfinityPrefix ++ msmStoreInfinityTail)
    .ok (restore V result.1, result.2.1, result.2.2)) = _
  rw [hbody]
  rfl

theorem eval_msmStoreInfinity (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("ptr", ptr)] yst (.call "\x0026" [.var "ptr"]) =
    .ok (.vals [] (msmStoreInfinityState yst ptr)) := by
  have hcall := Interp.evalExpr_call_normal
    (E := Challenge.EvmProof.modexpExec) (n := 67)
    (V := [("ptr", ptr)]) (st := yst) (args := [.var "ptr"])
    (argvals := [ptr]) (fn := "\x0026") (decl := msmStoreInfinityDecl)
    (cenv := fp2Funs) (Vend := [("\x00140", ptr)])
    (st2 := msmStoreInfinityState yst ptr)
    (by rfl) lookup_msmStoreInfinity (by rfl)
    (exec_msmStoreInfinityBody ptr yst)
  simpa [msmStoreInfinityDecl] using hcall

private theorem exec_msmCopyPointBody (dst src : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fp2Funs
      [("\x00141", dst), ("\x00142", src)] yst (.block msmCopyPointBody) =
    .ok ([("\x00141", dst), ("\x00142", src)],
      msmCopyPointState yst dst src, .normal) := by
  let V := [("\x00141", dst), ("\x00142", src)]
  have hpre : Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst msmCopyPointPrefix =
      .ok (V, msmCopyPointMidState yst dst src, .normal) := by rfl
  have htail : Interp.execStmts Challenge.EvmProof.modexpExec 62
      ([] :: fp2Funs) V (msmCopyPointMidState yst dst src)
      msmCopyPointTail =
      .ok (V, msmCopyPointState yst dst src, .normal) := by rfl
  have hbody := Interp.execStmts_append_normal
    (E := Challenge.EvmProof.modexpExec) (n := 62)
    (pre := msmCopyPointPrefix) (tail := msmCopyPointTail)
    (by omega) hpre htail
  have hlen : msmCopyPointPrefix.length = 4 := by rfl
  rw [hlen] at hbody
  rw [Interp.execStmt, msmCopyPointBody_eq]
  rw [show hoist Challenge.EvmProof.modexpExec.toDialect
    (msmCopyPointPrefix ++ msmCopyPointTail) = [] by rfl]
  change (do
    let result ← Interp.execStmts Challenge.EvmProof.modexpExec 66
      ([] :: fp2Funs) V yst (msmCopyPointPrefix ++ msmCopyPointTail)
    .ok (restore V result.1, result.2.1, result.2.2)) = _
  rw [hbody]
  rfl

theorem eval_msmCopyPoint (dst src : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("dst", dst), ("src", src)] yst
      (.call "\x0027" [.var "dst", .var "src"]) =
    .ok (.vals [] (msmCopyPointState yst dst src)) := by
  have hcall := Interp.evalExpr_call_normal
    (E := Challenge.EvmProof.modexpExec) (n := 67)
    (V := [("dst", dst), ("src", src)]) (st := yst)
    (args := [.var "dst", .var "src"]) (argvals := [dst, src])
    (fn := "\x0027") (decl := msmCopyPointDecl) (cenv := fp2Funs)
    (Vend := [("\x00141", dst), ("\x00142", src)])
    (st2 := msmCopyPointState yst dst src)
    (by rfl) lookup_msmCopyPoint (by rfl)
    (exec_msmCopyPointBody dst src yst)
  simpa [msmCopyPointDecl] using hcall

theorem eval_pointInfinity (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("ptr", ptr)] yst (.call "\x0028" [.var "ptr"]) =
    .ok (.vals [pointZeroValue yst ptr] (pointZeroReadState yst ptr)) := by
  rw [Interp.evalExpr, lookup_pointInfinity]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
