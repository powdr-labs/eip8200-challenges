import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Exact initialization of the frozen naive G1 scalar-multiplication loop. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def scalarMulStoreZero (yst : EvmState) (ptr : Nat) : EvmState :=
  { touchMemory yst ptr 32 with memory := storeWord yst.memory ptr 0 }

def scalarMulInitState (yst : EvmState) (out : U256) : EvmState :=
  scalarMulStoreZero
    (scalarMulStoreZero
      (scalarMulStoreZero
        (scalarMulStoreZero yst out.toNat)
        (out + 32).toNat)
      (out + 64).toNat)
    (out + 96).toNat

def scalarMulInitialBit : U256 :=
  EVM.litValue (.number
    57896044618658097711785492504343953926634992332820282019728792003956564819968)

def scalarMulInitEnv (scalar point out : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00145", scalarMulInitialBit)] ++
    scalarMulInitialEnv scalar point out

def scalarMulStoresBlock : Block Op :=
  [scalarMulStmt0, scalarMulStmt1, scalarMulStmt2, scalarMulStmt3,
    scalarMulStmt4, scalarMulStmt5]

theorem scalarMulInitBlock_eq : scalarMulInitBlock =
    scalarMulStoresBlock ++ [scalarMulStmt6] := by rfl

private theorem exec_scalarMulStores (yst : EvmState)
    (scalar point out : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 100 scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) yst scalarMulStoresBlock =
    .ok (scalarMulInitialEnv scalar point out,
      scalarMulInitState yst out, .normal) := by
  rfl

private theorem scalarMulStmt6_eq : scalarMulStmt6 =
    .letDecl ["\x00145"]
      (some (.lit (.number
        57896044618658097711785492504343953926634992332820282019728792003956564819968))) := by
  rfl

private theorem step_scalarMulBit (yst : EvmState) (scalar point out : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) (scalarMulInitState yst out)
      scalarMulStmt6 (scalarMulInitEnv scalar point out)
      (scalarMulInitState yst out) .normal := by
  rw [scalarMulStmt6_eq]
  simpa [scalarMulInitEnv, scalarMulInitialBit] using
    (Step.letVal
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := scalarMulBodyFuns)
      (V := scalarMulInitialEnv scalar point out)
      (st := scalarMulInitState yst out)
      (vars := ["\x00145"]) Step.lit rfl)

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

private theorem step_append_normal
    {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hpre : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vmid stmid .normal)
    (hsuffix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil =>
    cases hpre
    simpa using hsuffix
  | cons head rest ih =>
    cases hpre with
    | seqCons hhead htail =>
      simpa using Step.seqCons hhead (ih htail hsuffix)
    | seqStop _ hnot => exact (hnot rfl).elim

theorem step_scalarMulInit (yst : EvmState) (scalar point out : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) yst scalarMulInitBlock
      (scalarMulInitEnv scalar point out)
      (scalarMulInitState yst out) .normal := by
  rw [scalarMulInitBlock_eq]
  exact step_append_normal
    (soundStmts (exec_scalarMulStores yst scalar point out))
    (Step.seqCons (step_scalarMulBit yst scalar point out) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
