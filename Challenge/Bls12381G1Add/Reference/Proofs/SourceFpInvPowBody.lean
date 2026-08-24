import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowSuffix

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowReturnEnv (aHi aLo : U256) (decoded : MontResultValue) : VEnv D :=
  VEnv.setMany (fpPowInitialEnv aHi aLo) ["\x00126", "\x00125"]
    [decoded.lo, decoded.hi]

theorem restore_fpPowDecodedEnv (aHi aLo : U256)
    (base acc decoded : MontResultValue) :
    restore (fpPowInitialEnv aHi aLo)
      (fpPowDecodedEnv aHi aLo base acc decoded) =
      fpPowReturnEnv aHi aLo decoded := by
  rfl

inductive NativePowResult (aHi aLo resultHi resultLo : U256) : Prop
  | intro (base afterHigh afterLow decoded : MontResultValue)
      (hresultHi : resultHi = decoded.hi)
      (hresultLo : resultLo = decoded.lo)
      (hbase : NativeMontMulResult aLo aHi fpPowR2Lo fpPowR2Hi
        base.lo base.hi)
      (hhigh : NativeFoldDown base fpPowHighWordNat 124 base afterHigh)
      (hlow : NativeFoldDown base fpPowLowWordNat 256 afterHigh afterLow)
      (hdecode : NativeMontMulResult afterLow.lo afterLow.hi 1 0
        decoded.lo decoded.hi) :
      NativePowResult aHi aLo resultHi resultLo

private theorem execStmts_append_normal {funs : FunEnv D}
    {V0 V1 V2 : VEnv D} {st0 st1 st2 : EvmState} {pre tail : Block Op}
    (hpre : ExecStmts D funs V0 st0 pre V1 st1 .normal)
    (htail : ExecStmts D funs V1 st1 tail V2 st2 .normal) :
    ExecStmts D funs V0 st0 (pre ++ tail) V2 st2 .normal := by
  induction pre generalizing V0 st0 with
  | nil =>
      cases hpre
      simpa using htail
  | cons stmt rest ih =>
      cases hpre with
      | seqCons hstmt hrest =>
          exact Step.seqCons hstmt (ih hrest)
      | seqStop _ hnormal => exact (hnormal rfl).elim

theorem hoist_fpPowPMinus2Body : hoist D fpPowPMinus2Body = [] := by
  rw [fpPowBody_eq]
  rfl

theorem step_fpPowBody (aHi aLo : U256) (yst : EvmState) :
    ∃ resultHi resultLo,
      ExecStmt D fpInvFuns (fpPowInitialEnv aHi aLo) yst
        (.block fpPowPMinus2Body)
        (fpPowReturnEnv aHi aLo { lo := resultLo, hi := resultHi })
        yst .normal ∧
      NativePowResult aHi aLo resultHi resultLo := by
  obtain ⟨base, hprefix, hbaseNative, _hbaseInv⟩ :=
    step_fpPowPrefix aHi aLo yst
  obtain ⟨afterHigh, afterLow, hloops, hhighFold, hlowFold⟩ :=
    step_fpPowHighLow aHi aLo base yst
  obtain ⟨decoded, hsuffix, hdecodeNative⟩ :=
    step_fpPowSuffix aHi aLo base afterLow yst
  have hsuffixSeq : ExecStmts D fpPowBodyFuns
      (fpPowAccEnv aHi aLo base afterLow) yst [fpPowStmt5]
      (fpPowDecodedEnv aHi aLo base afterLow decoded) yst .normal :=
    Step.seqCons hsuffix Step.seqNil
  have hprefixLoops := execStmts_append_normal hprefix hloops
  have hall := execStmts_append_normal hprefixLoops hsuffixSeq
  have hbodySeq : ExecStmts D fpPowBodyFuns (fpPowInitialEnv aHi aLo) yst
      fpPowPMinus2Body (fpPowDecodedEnv aHi aLo base afterLow decoded)
      yst .normal := by
    rw [fpPowBody_eq]
    simpa using hall
  have hbodySeq' : ExecStmts D (hoist D fpPowPMinus2Body :: fpInvFuns)
      (fpPowInitialEnv aHi aLo) yst fpPowPMinus2Body
      (fpPowDecodedEnv aHi aLo base afterLow decoded) yst .normal := by
    simpa [fpPowBodyFuns, hoist_fpPowPMinus2Body] using hbodySeq
  have hblock := Step.block (funs := fpInvFuns) hbodySeq'
  rw [restore_fpPowDecodedEnv] at hblock
  refine ⟨decoded.hi, decoded.lo, hblock, ?_⟩
  exact NativePowResult.intro base afterHigh afterLow decoded rfl rfl
    hbaseNative hhighFold hlowFold hdecodeNative

theorem fpPowReturnEnv_hi (aHi aLo resultHi resultLo : U256) :
    (VEnv.get (fpPowReturnEnv aHi aLo { lo := resultLo, hi := resultHi })
      "\x00125").getD 0 = resultHi := by rfl

theorem fpPowReturnEnv_lo (aHi aLo resultHi resultLo : U256) :
    (VEnv.get (fpPowReturnEnv aHi aLo { lo := resultLo, hi := resultHi })
      "\x00126").getD 0 = resultLo := by rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
