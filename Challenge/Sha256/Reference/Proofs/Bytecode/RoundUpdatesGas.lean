import Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGasBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private theorem potential_trans {a b p q r k l : Nat}
    (h₁ : a + p = k + q) (h₂ : b + q = l + r) :
    (a + b) + p = (k + l) + r := by
  omega

private theorem shift_cost_potential
    (loadPath storePath : List
      (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (q : State) (src dest loadReturn storeReturn startPC loadWork storeWork : Nat)
    (context : List UInt256)
    (hload :
      (loadPath = Compression.shift76Path ∧ src = 6 ∧ loadReturn = 796 ∧
        storeReturn = 803 ∧ startPC = 783) ∨
      (loadPath = Compression.shift65Path ∧ src = 5 ∧ loadReturn = 817 ∧
        storeReturn = 824 ∧ startPC = 803) ∨
      (loadPath = Compression.shift32Path ∧ src = 2 ∧ loadReturn = 872 ∧
        storeReturn = 879 ∧ startPC = 858) ∨
      (loadPath = Compression.shift21Path ∧ src = 1 ∧ loadReturn = 893 ∧
        storeReturn = 900 ∧ startPC = 879))
    (hstore :
      (storePath = Compression.store7Path ∧ src = 6 ∧ dest = 7 ∧
        loadReturn = 796 ∧ storeReturn = 803) ∨
      (storePath = Compression.store6Path ∧ src = 5 ∧ dest = 6 ∧
        loadReturn = 817 ∧ storeReturn = 824) ∨
      (storePath = Compression.store3Path ∧ src = 2 ∧ dest = 3 ∧
        loadReturn = 872 ∧ storeReturn = 879) ∨
      (storePath = Compression.store2Path ∧ src = 1 ∧ dest = 2 ∧
        loadReturn = 893 ∧ storeReturn = 900))
    (hpc : q.pc = UInt256.ofNat startPC) (hstack : q.stack = context)
    (hcap : context.length < 1016)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hfork : q.fork = .Osaka) (hrun : q.halt = .Running)
    (hnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false)
    (hloadWork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost loadPath =
      loadWork)
    (hstoreWork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost storePath =
      storeWork) :
    (Compression.gasSteps_shift loadPath storePath q src dest loadReturn
      storeReturn startPC context hload hstore hpc hstack hcap hcode hfork hrun
      hnp).cost + MachineState.memCost q.activeWords.toNat =
      loadWork + 37 + storeWork + 34 + MachineState.memCost
        (Compression.shiftReturned q src dest loadReturn storeReturn context).activeWords.toNat := by
  have hsetupLoad := blockCost_potential_of_static loadPath loadWork
    (Compression.run_shiftLoad loadPath q src loadReturn storeReturn startPC
      context hload hpc hstack (by omega) hcode hrun) hfork
    (by rcases hload with h | h | h | h <;>
        rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
        simp [Compression.shift76Path, Compression.shift65Path,
          Compression.shift32Path, Compression.shift21Path, CopyFree])
    hloadWork
  have hget := CompressionGas.hAt_cost_potential q (UInt256.ofNat src) 0
    (UInt256.ofNat loadReturn) (UInt256.ofNat storeReturn :: context)
    (by simp; omega) hcode hfork hrun hnp (by
      rcases hload with h | h | h | h <;>
        rcases h with ⟨_, rfl, rfl, rfl, _⟩ <;> decide)
  have qLoadedCode :
      (Compression.shiftLoaded q src loadReturn storeReturn context).executionEnv.code =
        referenceBytecode := by
    simpa [Compression.shiftLoaded, Accessors.loadReturned] using hcode
  have qLoadedFork :
      (Compression.shiftLoaded q src loadReturn storeReturn context).fork =
        .Osaka := by
    simpa [Compression.shiftLoaded, Accessors.loadReturned, State.fork]
      using hfork
  have qLoadedRun :
      (Compression.shiftLoaded q src loadReturn storeReturn context).halt =
        .Running := by
    simpa [Compression.shiftLoaded, Accessors.loadReturned] using hrun
  have qLoadedNp : Precompile.isPrecompile
      (Compression.shiftLoaded q src loadReturn storeReturn context).executionEnv.fork
      (Compression.shiftLoaded q src loadReturn storeReturn context).executionEnv.codeAddr =
        false := by
    simpa [Compression.shiftLoaded, Accessors.loadReturned] using hnp
  have hsetupStore := blockCost_potential_of_static storePath storeWork
    (Compression.run_shiftStore storePath q src dest loadReturn storeReturn
      context hstore (by omega) hcode hrun) qLoadedFork
    (by rcases hstore with h | h | h | h <;>
        rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
        simp [Compression.store7Path, Compression.store6Path,
          Compression.store3Path, Compression.store2Path, CopyFree])
    hstoreWork
  have hset := CompressionGas.hSet_cost_potential
    (Compression.shiftLoaded q src loadReturn storeReturn context)
    (UInt256.ofNat dest) (Compression.hValue q src)
    (UInt256.ofNat storeReturn) context (by omega) qLoadedCode qLoadedFork
    qLoadedRun qLoadedNp (by
      rcases hstore with h | h | h | h <;>
        rcases h with ⟨_, rfl, rfl, rfl, rfl⟩ <;> decide)
  have hawLoad :
      (Compression.shiftLoadEntry q src loadReturn storeReturn context).activeWords =
        q.activeWords := by rfl
  have hawStore :
      (Compression.shiftStoreEntry q src dest loadReturn storeReturn context).activeWords =
        (Compression.shiftLoaded q src loadReturn storeReturn context).activeWords := by
    rfl
  unfold Compression.gasSteps_shift
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [hawLoad] at hsetupLoad
  rw [hawStore] at hsetupStore
  change _ = 37 + MachineState.memCost
    (Compression.shiftLoaded q src loadReturn storeReturn context).activeWords.toNat at hget
  change _ = 34 + MachineState.memCost
    (Compression.shiftReturned q src dest loadReturn storeReturn context).activeWords.toNat at hset
  omega

theorem updates_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_updates s msgOff returnDest rest j hj hcap hcode
      hfork hrun hnp).cost + MachineState.memCost
        (Compression.afterT2 s msgOff returnDest rest j).activeWords.toNat =
      634 + MachineState.memCost
        (Compression.afterSecondIteration s msgOff returnDest rest j).activeWords.toNat := by
  let ctx := Compression.roundContext s msgOff returnDest rest j
  have hctx : ctx.length < 1016 := by simp [ctx, Compression.roundContext]; omega
  let q0 := Compression.afterT2 s msgOff returnDest rest j
  have q0code : q0.executionEnv.code = referenceBytecode := by
    simpa [q0] using hcode
  have q0fork : q0.fork = .Osaka := by simpa [q0, State.fork] using hfork
  have q0run : q0.halt = .Running := by simpa [q0] using hrun
  have q0np : Precompile.isPrecompile q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by simpa [q0] using hnp
  have hs7 := shift_cost_potential Compression.shift76Path
    Compression.store7Path q0 6 7 796 803 783 22 15 ctx
    (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) (by rfl) (by rfl) hctx
    q0code q0fork q0run q0np (by rfl) (by rfl)
  let q1 := Compression.afterShift7 s msgOff returnDest rest j
  have q1code : q1.executionEnv.code = referenceBytecode := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q0code
  have q1fork : q1.fork = .Osaka := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q0fork
  have q1run : q1.halt = .Running := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q0run
  have q1np : Precompile.isPrecompile q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, q0, Compression.afterShift7, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q0np
  have hs6 := shift_cost_potential Compression.shift65Path
    Compression.store6Path q1 5 6 817 824 803 23 15 ctx
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
    (by rfl) (by rfl) hctx q1code q1fork q1run q1np (by rfl) (by rfl)
  let q2 := Compression.afterShift6 s msgOff returnDest rest j
  have q2code : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q1code
  have q2fork : q2.fork = .Osaka := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q1fork
  have q2run : q2.halt = .Running := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q1run
  have q2np : Precompile.isPrecompile q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, q1, Compression.afterShift6, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q1np
  have hstoreE := blockCost_potential_of_static Compression.storeEPath 10
    (Compression.run_storeE s msgOff returnDest rest j (by omega) hrun)
    q2fork (by simp [Compression.storeEPath, CopyFree]) (by rfl)
  let q3 := Compression.afterStoreE s msgOff returnDest rest j
  have q3code : q3.executionEnv.code = referenceBytecode := by
    simpa [q3, Compression.afterStoreE, Compression.directStored] using q2code
  have q3fork : q3.fork = .Osaka := by
    simpa [q3, Compression.afterStoreE, Compression.directStored, State.fork]
      using q2fork
  have q3run : q3.halt = .Running := by
    simpa [q3, Compression.afterStoreE, Compression.directStored] using q2run
  have q3np : Precompile.isPrecompile q3.executionEnv.fork
      q3.executionEnv.codeAddr = false := by
    simpa [q3, Compression.afterStoreE, Compression.directStored] using q2np
  have hsetupH4 := blockCost_potential_of_static
    Compression.setupH3ForH4Path 28
    (Compression.run_setupH3ForH4 s msgOff returnDest rest j (by omega)
      hcode hrun) q3fork
    (by simp [Compression.setupH3ForH4Path, CopyFree]) (by rfl)
  have hgetH4 := CompressionGas.hAt_cost_potential q3 (UInt256.ofNat 3) 0
    (UInt256.ofNat 849)
    ([Compression.t1 s j, UInt256.ofNat 0xffffffff, UInt256.ofNat 858] ++ ctx)
    (by simp [ctx, Compression.roundContext]; omega) q3code q3fork q3run q3np
    (by decide)
  have hstoreH4 := blockCost_potential_of_static Compression.storeH4Path 21
    (Compression.run_storeH4 s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.h4Loaded, Accessors.loadReturned, State.fork]
      using q3fork)
    (by simp [Compression.storeH4Path, CopyFree]) (by rfl)
  have hsetH4 := CompressionGas.hSet_cost_potential
    (Compression.h4Loaded s msgOff returnDest rest j) (UInt256.ofNat 4)
    (Compression.newH4 s msgOff returnDest rest j) (UInt256.ofNat 858) ctx
    (by simp [ctx, Compression.roundContext]; omega)
    (by simpa [Compression.h4Loaded, Accessors.loadReturned] using q3code)
    (by simpa [Compression.h4Loaded, Accessors.loadReturned, State.fork]
      using q3fork)
    (by simpa [Compression.h4Loaded, Accessors.loadReturned] using q3run)
    (by simpa [Compression.h4Loaded, Accessors.loadReturned] using q3np)
    (by decide)
  let q4 := Compression.afterStoreH4 s msgOff returnDest rest j
  have q4code : q4.executionEnv.code = referenceBytecode := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned] using q3code
  have q4fork : q4.fork = .Osaka := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned, State.fork] using q3fork
  have q4run : q4.halt = .Running := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned] using q3run
  have q4np : Precompile.isPrecompile q4.executionEnv.fork
      q4.executionEnv.codeAddr = false := by
    simpa [q4, Compression.afterStoreH4, Accessors.storeReturned,
      Compression.h4Loaded, Accessors.loadReturned] using q3np
  have hs3 := shift_cost_potential Compression.shift32Path
    Compression.store3Path q4 2 3 872 879 858 23 15 ctx
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    (by rfl) (by rfl) hctx q4code q4fork q4run q4np (by rfl) (by rfl)
  let q5 := Compression.afterShift3 s msgOff returnDest rest j
  have q5code : q5.executionEnv.code = referenceBytecode := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q4code
  have q5fork : q5.fork = .Osaka := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q4fork
  have q5run : q5.halt = .Running := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q4run
  have q5np : Precompile.isPrecompile q5.executionEnv.fork
      q5.executionEnv.codeAddr = false := by
    simpa [q5, Compression.afterShift3, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned] using q4np
  let q5rawState := Compression.shiftReturned q4 2 3 872 879 ctx
  have q5rawCode : q5rawState.executionEnv.code = referenceBytecode := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned] using q4code
  have q5rawFork : q5rawState.fork = .Osaka := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned, State.fork] using q4fork
  have q5rawRun : q5rawState.halt = .Running := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned] using q4run
  have q5rawNp : Precompile.isPrecompile q5rawState.executionEnv.fork
      q5rawState.executionEnv.codeAddr = false := by
    simpa [q5rawState, Compression.shiftReturned, Accessors.storeReturned,
      Compression.shiftLoaded, Accessors.loadReturned] using q4np
  have hs2 := shift_cost_potential Compression.shift21Path
    Compression.store2Path q5rawState 1 2 893 900 879 23 15 ctx
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    (by rfl) (by rfl) hctx q5rawCode q5rawFork q5rawRun q5rawNp
    (by rfl) (by rfl)
  have hfinish := blockCost_potential_of_static Compression.finishRoundPath 69
    (Compression.run_finishRound s msgOff returnDest rest j hj (by omega)
      hcode hrun)
    (by simpa [Compression.afterShift2, Compression.shiftReturned,
      Accessors.storeReturned, Compression.shiftLoaded,
      Accessors.loadReturned, State.fork] using q5fork)
    (by simp [Compression.finishRoundPath, CopyFree]) (by rfl)
  unfold Compression.gasSteps_updates
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  have hawH4Load :
      (Compression.h4LoadEntry s msgOff returnDest rest j).activeWords =
        q3.activeWords := by rfl
  have hawH4Store :
      (Compression.h4StoreEntry s msgOff returnDest rest j).activeWords =
        (Compression.h4Loaded s msgOff returnDest rest j).activeWords := by rfl
  rw [hawH4Load] at hsetupH4
  rw [hawH4Store] at hstoreH4
  change _ = 37 + MachineState.memCost
    (Compression.h4Loaded s msgOff returnDest rest j).activeWords.toNat at hgetH4
  change _ = 34 + MachineState.memCost
    q4.activeWords.toNat at hsetH4
  change _ = 108 + MachineState.memCost q1.activeWords.toNat at hs7
  change _ = 109 + MachineState.memCost q2.activeWords.toNat at hs6
  change _ = 109 + MachineState.memCost q5rawState.activeWords.toNat at hs3
  change _ = 109 + MachineState.memCost
    (Compression.afterShift2 s msgOff returnDest rest j).activeWords.toNat at hs2
  dsimp only [q0, q1, q2, q3, q4, q5, q5rawState, ctx] at *
  have h₁ := potential_trans hs7 hs6
  have h₂ := potential_trans h₁ hstoreE
  have h₃ := potential_trans h₂ hsetupH4
  have h₄ := potential_trans h₃ hgetH4
  have h₅ := potential_trans h₄ hstoreH4
  have h₆ := potential_trans h₅ hsetH4
  have h₇ := potential_trans h₆ hs3
  have h₈ := potential_trans h₇ hs2
  have h₉ := potential_trans h₈ hfinish
  unfold Compression.gasSteps_shift at h₉ ⊢
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Compression.afterShift2, Compression.afterShift3] at h₉ ⊢
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h₉


end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
