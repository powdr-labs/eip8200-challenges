import Challenge.Bls12381G1Msm.Reference.Proofs.SourceInvalidLengthPrefix
import Challenge.Bls12381G1Msm.SpecRefinement

set_option warningAsError true

/-! Executable size and invalid-branch lemmas for G1MSM. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

private theorem sound_execStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt modexpExec.toDialect funs V st stmt V' st' outcome :=
  (Interp.sound_all_of
    (E := modexpExec)
    (fun _ _ _ _ hbuiltin => modexpBuiltinFn_sound hbuiltin) n).2.2.1
    _ _ _ _ _ _ _ h

def sizeEnv (yst : EvmState) (V : VEnv modexpExec.toDialect) :
    VEnv modexpExec.toDialect :=
  (sizeName, BitVec.ofNat 256 yst.env.calldata.length) :: V

private theorem lengthWord_mod_ne {yst : EvmState}
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hrem : yst.env.calldata.length % Challenge.Bls12381G1Msm.pairBytes ≠ 0) :
    BitVec.ofNat 256 yst.env.calldata.length % BitVec.ofNat 256 160 ≠ 0 := by
  intro hzero
  have hnat := congrArg BitVec.toNat hzero
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hfit] at hnat
  norm_num at hnat
  exact hrem (by simpa [Challenge.Bls12381G1Msm.pairBytes] using hnat)

theorem exec_invalidLengthStmt {yst : EvmState} (funs V)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hbad : yst.env.calldata.length = 0 ∨
      yst.env.calldata.length % Challenge.Bls12381G1Msm.pairBytes ≠ 0) :
    Interp.execStmt modexpExec 114 funs (sizeEnv yst V) yst invalidLengthStmt =
      .ok (sizeEnv yst V, { yst with halted := some (.invalid, []) }, .halt) := by
  rcases hbad with hzero | hrem
  · simp [invalidLengthStmt, sizeEnv, sizeName, Interp.execStmt,
      Interp.execStmts, Interp.evalExpr, Interp.evalArgs, modexpExec,
      modexpBuiltinFn, stepOp, bin, un, litValue, b2w, Dialect.zero,
      VEnv.get, restore, hzero]
  · have hmod := lengthWord_mod_ne hfit hrem
    simp [invalidLengthStmt, sizeEnv, sizeName, Interp.execStmt,
      Interp.execStmts, Interp.evalExpr, Interp.evalArgs, modexpExec,
      modexpBuiltinFn, stepOp, bin, un, litValue, b2w, Dialect.zero,
      VEnv.get, restore]
    exact fun _ => hmod

theorem exec_sizeStmt (yst : EvmState) (funs V) :
    Interp.execStmt modexpExec 115 funs V yst sizeStmt =
      .ok (sizeEnv yst V, yst, .normal) := by
  simp [sizeStmt, sizeEnv, sizeName, Interp.execStmt, Interp.evalExpr,
    Interp.evalArgs, modexpExec, modexpBuiltinFn, stepOp, rd0]

theorem step_invalidLengthStmt {yst : EvmState} (funs V)
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hbad : yst.env.calldata.length = 0 ∨
      yst.env.calldata.length % Challenge.Bls12381G1Msm.pairBytes ≠ 0) :
    ExecStmt modexpExec.toDialect funs (sizeEnv yst V) yst
      invalidLengthStmt (sizeEnv yst V)
      { yst with halted := some (.invalid, []) } .halt :=
  sound_execStmt (exec_invalidLengthStmt funs V hfit hbad)

theorem step_sizeStmt (yst : EvmState) (funs V) :
    ExecStmt modexpExec.toDialect funs V yst sizeStmt
      (sizeEnv yst V) yst .normal :=
  sound_execStmt (exec_sizeStmt yst funs V)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
