import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.ProfiledCalls
set_option warningAsError true
/-!
# Concrete EVM realization of successful MODEXP calls

This module discharges `ProfiledCallsRealized` for the narrow source relation
in `ModexpCalls`.  The proof follows the actual EVM trace: STATICCALL enters a
child frame, native MODEXP returns, and the caller frame resumes successfully.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open YulEvmCompiler

/-- State-independent ceiling for the committed part of an Osaka STATICCALL. -/
theorem staticcallCommitted_le (s : State)
    (hfork : s.executionEnv.fork = .Osaka)
    (argsOff argsLen retOff retLen toArg : UInt256) :
    Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg ≤
      5200 + memBound argsOff.toNat argsLen.toNat +
        memBound retOff.toNat retLen.toNat := by
  have hbase : Gas.baseCost s.executionEnv.fork .STATICCALL ≤ 100 := by
    rw [hfork]
    decide
  have hmem := memExpansionDelta2_le_memBounds s.activeWords.toNat
    argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
  have hcold : Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg) ≤ 2500 := by
    unfold Gas.accountColdSurcharge
    split_ifs <;> omega
  have hdel : Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg) ≤ 2600 := by
    unfold Gas.delegationAccessCost
    split <;> first | (split_ifs <;> omega) | omega
  unfold Gas.staticcallCommitted
  omega

/-- Enough post-commit gas makes the EIP-150 cap retain the requested gas. -/
theorem forwardGas_eq_arg_of_65_mul_le (available requested : Nat)
    (h : 65 * requested ≤ available) :
    Gas.forwardGas .Osaka available requested = requested := by
  have hcap : requested ≤ available - available / 64 := by
    apply (Nat.le_sub_iff_add_le (Nat.div_le_self available 64)).2
    have hdiv : available / 64 ≤ available - requested := by
      apply (Nat.div_le_iff_le_mul (by omega : 0 < 64)).2
      omega
    omega
  simp [Gas.forwardGas, hcap]

/-- A successful MODEXP result never reports more gas than was supplied. -/
theorem runModexp_success_gas_le {fork : Fork} {input : ByteArray}
    {childGas gasUsed : Nat} {output : ByteArray}
    (h : Precompile.runModexp fork input childGas = .success output gasUsed) :
    gasUsed ≤ childGas := by
  unfold Precompile.runModexp at h
  dsimp only at h
  split at h
  · contradiction
  split at h
  · rename_i hcost
    split at h <;> injection h
    all_goals omega
  · contradiction

/-- Configured precompile dispatch at address `0x05` is exactly MODEXP. -/
theorem runWithConfig_modexp (config : PrecompileConfig) (input : ByteArray)
    (gas : Nat)
    (h : Precompile.isPrecompileWithConfig config .Osaka
      Precompile.modexpAddress = true) :
    Precompile.runWithConfig config .Osaka Precompile.modexpAddress input gas h =
      Precompile.runModexp .Osaka input gas := by
  unfold Precompile.runWithConfig
  unfold Precompile.run
  have hne1 : Precompile.modexpAddress ≠ Precompile.ecrecoverAddress := by
    intro heq
    have hv := congrArg Fin.val heq
    norm_num [Precompile.modexpAddress, Precompile.ecrecoverAddress,
      AccountAddress.ofUInt256, toNat_u256_ofNat, AccountAddress.size] at hv
  have hne2 : Precompile.modexpAddress ≠ Precompile.sha256Address := by
    intro heq
    have hv := congrArg Fin.val heq
    norm_num [Precompile.modexpAddress, Precompile.sha256Address,
      AccountAddress.ofUInt256, toNat_u256_ofNat, AccountAddress.size] at hv
  have hne3 : Precompile.modexpAddress ≠ Precompile.ripemd160Address := by
    intro heq
    have hv := congrArg Fin.val heq
    norm_num [Precompile.modexpAddress, Precompile.ripemd160Address,
      AccountAddress.ofUInt256, toNat_u256_ofNat, AccountAddress.size] at hv
  have hne4 : Precompile.modexpAddress ≠ Precompile.identityAddress := by
    intro heq
    have hv := congrArg Fin.val heq
    norm_num [Precompile.modexpAddress, Precompile.identityAddress,
      AccountAddress.ofUInt256, toNat_u256_ofNat, AccountAddress.size] at hv
  rw [dif_neg hne1, dif_neg hne2, dif_neg hne3, dif_neg hne4]
  have hmx : Fork.Osaka ≥ Fork.Byzantium ∧
      Precompile.modexpAddress = Precompile.modexpAddress := ⟨by decide, rfl⟩
  rw [dif_pos hmx]

/-- The narrow successful-MODEXP source relation is realized by the real
Osaka STATICCALL/precompile/return trace under an enabled caller profile. -/
theorem successfulModexpCalls_realized (config : PrecompileConfig)
    (henabled : Precompile.isPrecompileWithConfig config .Osaka
      Precompile.modexpAddress = true) :
    ProfiledCallsRealized successfulModexpCalls config := by
  constructor
  intro yop hcall o hop args rets yst yst' hsource
  have hkinds : yop = .call ∨ yop = .callcode ∨ yop = .delegatecall ∨
      yop = .staticcall := by
    cases yop <;> simp_all [IsCallOp]
  rcases hkinds with rfl | rfl | rfl | rfl
  · rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨value, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.externalCall, successfulModexpCalls] at hsource
    split at hsource
    · contradiction
    · obtain ⟨response, hCall, -⟩ := hsource
      exact (by simpa using hCall.kind : False).elim
  · rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨value, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.externalCall, successfulModexpCalls] at hsource
    obtain ⟨response, hCall, -⟩ := hsource
    exact (by simpa using hCall.kind : False).elim
  · rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.externalCall, successfulModexpCalls] at hsource
    obtain ⟨response, hCall, -⟩ := hsource
    exact (by simpa using hCall.kind : False).elim
  · have hoSTATICCALL : o = .STATICCALL := by
      have h : opTable Op.staticcall = some Operation.STATICCALL := rfl
      rw [h] at hop
      exact (Option.some.inj hop).symm
    subst hoSTATICCALL
    rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.externalCall] at hsource
    obtain ⟨response, hCall, heq⟩ := hsource
    injection heq with hrets hyst'
    subst hyst'
    subst rets
    unfold successfulModexpCalls at hCall
    obtain ⟨hkind, htarget, hvalue, output, gasUsed, hresult, hsuccess,
      hreturndata, hworld⟩ := hCall
    change target = BitVec.ofNat 256 5 at htarget
    subst target
    change Precompile.runModexp .Osaka
      ⟨(YulSemantics.EVM.readBytes yst.memory inOff.toNat inSize.toNat).toArray⟩
      gas.toNat = .success output gasUsed at hresult
    refine ⟨5200 + memBound inOff.toNat inSize.toNat +
      memBound outOff.toNat outSize.toNat + 65 * gas.toNat, ?_⟩
    intro code s σ hf hm hprofile hdec hstk hbnd hcap
    have hstk' : s.stack = conv gas :: UInt256.ofNat 5 :: conv inOff ::
        conv inSize :: conv outOff :: conv outSize :: σ := by
      simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        conv_ofNat'] using hstk
    have hcommitted := staticcallCommitted_le s hf.fork (conv inOff) (conv inSize)
      (conv outOff) (conv outSize) (UInt256.ofNat 5)
    simp only [conv_toNat] at hcommitted
    have hgas : Gas.staticcallCommitted s (conv inOff) (conv inSize)
        (conv outOff) (conv outSize) (UInt256.ofNat 5) ≤ s.gasAvailable := by
      omega
    have hpost : 65 * gas.toNat ≤ s.gasAvailable -
        Gas.staticcallCommitted s (conv inOff) (conv inSize)
          (conv outOff) (conv outSize) (UInt256.ofNat 5) := by
      omega
    have hfwd : gas.toNat = Gas.forwardGas s.executionEnv.fork
        (s.gasAvailable - Gas.staticcallCommitted s (conv inOff) (conv inSize)
          (conv outOff) (conv outSize) (UInt256.ofNat 5)) gas.toNat := by
      rw [hf.fork]
      exact (forwardGas_eq_arg_of_65_mul_le _ _ hpost).symm
    have hafford : gas.toNat ≤ s.gasAvailable -
        Gas.staticcallCommitted s (conv inOff) (conv inSize)
          (conv outOff) (conv outSize) (UInt256.ofNat 5) := by
      omega
    let sCall :=
      (({ s with
          gasAvailable := s.gasAvailable - Gas.staticcallCommitted s
            (conv inOff) (conv inSize) (conv outOff) (conv outSize) (UInt256.ofNat 5) -
              gas.toNat
          activeWords := s.activeWordsAfterUInt256_2 inOff.toNat inSize.toNat
            outOff.toNat outSize.toNat }).enterCallFor .StaticCall σ
        Precompile.modexpAddress ⟨0⟩
        (MachineState.readPadded s.memory inOff.toNat inSize.toNat)
        (State.callTargetCode s Precompile.modexpAddress) gas.toNat
        outOff.toNat outSize.toNat)
    have hstepCall : Step s sCall := by
      apply Step.running hf.running hf.noPrecompile
      simpa only [sCall, Precompile.modexpAddress, conv_toNat] using
        (StepRunning.staticcall s (conv gas) (UInt256.ofNat 5) (conv inOff)
          (conv inSize) (conv outOff) (conv outSize) σ gas.toNat hdec hstk' hgas
          (Nat.not_le_of_lt hprofile.depth) hfwd hafford hcap)
    have hinput :
        ⟨(YulSemantics.EVM.readBytes yst.memory inOff.toNat inSize.toNat).toArray⟩ =
          MachineState.readPadded s.memory inOff.toNat inSize.toNat := by
      change mkCode (YulSemantics.EVM.readBytes yst.memory inOff.toNat inSize.toNat) = _
      rw [hm.mem.readBytes, mkCode_toList]
    have hsCallRunning : sCall.halt = .Running := by
      simp [sCall, State.enterCallFor]
    have hsCallPrec : Precompile.isPrecompileWithConfig
        sCall.executionEnv.precompileConfig sCall.executionEnv.fork
          sCall.executionEnv.codeAddr = true := by
      simpa [sCall, State.enterCallFor, State.calleeEnvFor,
        hprofile.precompileConfig, hf.fork] using henabled
    have htargetResult : Precompile.runWithConfig config .Osaka
        Precompile.modexpAddress
          (MachineState.readPadded s.memory inOff.toNat inSize.toNat)
          gas.toNat henabled = .success output gasUsed := by
      rw [runWithConfig_modexp, ← hinput]
      exact hresult
    have hsCallResult : Precompile.runWithConfig sCall.executionEnv.precompileConfig
        sCall.executionEnv.fork sCall.executionEnv.codeAddr sCall.executionEnv.calldata
          sCall.gasAvailable hsCallPrec = .success output gasUsed := by
      simpa only [sCall, State.enterCallFor, State.calleeEnvFor,
        hprofile.precompileConfig, hf.fork] using htargetResult
    let sPrec : State :=
      { sCall with
        halt := .Returned
        hReturn := output
        gasAvailable := sCall.gasAvailable - gasUsed }
    have hstepPrec : Step sCall sPrec := by
      simpa only [sPrec] using
        Step.precompileSuccess sCall output gasUsed hsCallRunning hsCallPrec hsCallResult
    let sReturn := sPrec.resumeSuccess sPrec.callStack.head! []
    have hstepReturn : Step sPrec sReturn := by
      apply Step.returning
      apply StepReturn.callReturnSuccess sPrec sPrec.callStack.head! []
      · exact Or.inr (by simp [sPrec])
      · simp [sPrec, sCall, State.enterCallFor, hf.callStack]
      · simp [sPrec, sCall, State.enterCallFor, hf.callStack]
    let sDone : State :=
      { s with
        gasAvailable :=
          (s.gasAvailable - Gas.staticcallCommitted s (conv inOff) (conv inSize)
              (conv outOff) (conv outSize) (UInt256.ofNat 5) - gas.toNat) +
            (gas.toNat - gasUsed)
        activeWords := s.activeWordsAfterUInt256_2 inOff.toNat inSize.toNat
          outOff.toNat outSize.toNat
        memory := State.writeReturn s.memory output outOff.toNat outSize.toNat
        returnData := output
        hReturn := output
        substate := State.warmCallTarget s s.substate Precompile.modexpAddress
        pc := s.pc.succ
        stack := UInt256.ofNat 1 :: σ
        halt := .Running
        callStack := [] }
    have hsReturn : sReturn = sDone := by
      simp [sReturn, sDone, sPrec, sCall, State.resumeSuccess, State.resumeWith,
        State.enterCallFor, State.calleeEnvFor, hf.callStack,
        State.warmCallTarget, State.delegateOf, CallKind.transfersValue,
        UInt256.succ, Precompile.modexpAddress]
      rfl
    have hwarm : ∀ {α : Type} (f : Substate → α),
        (∀ A a, f (Substate.addAccessedAccount A a) = f A) →
        f (State.warmCallTarget s s.substate Precompile.modexpAddress) =
          f s.substate := by
      intro α f hinvariant
      unfold State.warmCallTarget Substate.addAccessedAccountOpt
      cases s.delegateOf Precompile.modexpAddress <;> simp only [hinvariant]
    refine ⟨sReturn, .trans hstepCall (.trans hstepPrec (.trans hstepReturn (.refl _))),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsReturn]
      exact ⟨hf.hcode, hf.codeSmall, hf.fork, hf.noPrecompile, rfl, rfl⟩
    · rw [hsReturn]
      refine {
        mem := ?_
        stor := ?_
        tstor := ?_
        cd := ?_
        env := ?_
        codeBytes := ?_
        codeLen := ?_
        selfBalance := ?_
        balanceOf := ?_
        activeWords := ?_
        retData := ?_
        retDataLen := ?_
        externalCode := ?_
        logs := ?_
        selfdestructs := ?_
        createdThisTx := ?_ }
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          hreturndata] using
          (Challenge.EvmProof.MemMatch.copyReturn hm.mem outOff.toNat
            outSize.toNat output)
      · intro key
        simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using
          hm.stor key
      · intro key
        simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using
          hm.tstor key
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using hm.cd
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using hm.env
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using
          hm.codeBytes
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using
          hm.codeLen
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using
          hm.selfBalance
      · intro address
        simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using
          hm.balanceOf address
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess] using
          (activeWordsAfter2_eq hm.activeWords inOff.toNat inSize.toNat
            outOff.toNat outSize.toNat inOff.isLt inSize.isLt)
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          hreturndata] using
          (Challenge.EvmProof.MemMatch.byteFrom_toList output)
      · simp [sDone, YulSemantics.EVM.finishCall, hsuccess,
          hreturndata, ByteArray.toList_eq_data]
      · simpa [sDone, YulSemantics.EVM.finishCall, hsuccess,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory] using
          hm.externalCode
      · simp only [sDone, YulSemantics.EVM.finishCall, hsuccess,
          ne_eq, not_true_eq_false, and_false, if_false,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory]
        rw [hwarm (fun A => A.logSeries) (fun _ _ => rfl)]
        exact hm.logs
      · simp only [sDone, YulSemantics.EVM.finishCall, hsuccess,
          ne_eq, not_true_eq_false, and_false, if_false,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory]
        rw [hwarm (fun A => A.selfDestructList) (fun _ _ => rfl),
          hwarm (fun A => A.originalAccountMap) (fun _ _ => rfl)]
        exact hm.selfdestructs
      · simp only [sDone, YulSemantics.EVM.finishCall, hsuccess,
          ne_eq, not_true_eq_false, and_false, if_false,
          YulSemantics.EVM.touchMemory2, YulSemantics.EVM.touchMemory]
        rw [hwarm (fun A => A.originalAccountMap) (fun _ _ => rfl)]
        exact hm.createdThisTx
    · rw [hsReturn]
      exact ⟨by simpa [sDone] using hprofile.depth,
        by simpa [sDone] using hprofile.precompileConfig⟩
    · simp [hsReturn, sDone]
    · rw [hsReturn]
      simp [sDone, YulSemantics.EVM.CallResponse.flag, hsuccess, conv_ofNat']
    · rw [hsReturn]
      simp only [sDone]
      have hused := runModexp_success_gas_le hresult
      omega

end Challenge.EvmProof
