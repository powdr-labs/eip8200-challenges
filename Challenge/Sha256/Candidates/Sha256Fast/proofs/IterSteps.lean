import Rounds8
set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! The rounds-loop iteration: chaining the block lemmas of `Rounds8`.
Split from the artifact file so composition work recompiles in seconds
against `Rounds8.olean` instead of re-elaborating the blocks (~12 min). -/

namespace Loop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word Challenge.Sha256.Fast
open EvmSemantics.Crypto.Sha256

private theorem step0 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 912)
    (hstack : s.stack =
      [ofUInt32 S0, ofUInt32 S1, ofUInt32 S2, ofUInt32 S3, ofUInt32 S4, ofUInt32 S5, ofUInt32 S6, ofUInt32 S7] ++ q :: rest)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2432 + q).toNat = ofUInt32 Kc0)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 384 + q).toNat = dbl (ofUInt32 Wt0)) :
    runLocatedBlock pround0 s =
      some { s with
        pc := UInt256.ofNat 1008
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 S0,
      ofUInt32 S1,
      ofUInt32 S2,
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 S4,
      ofUInt32 S5,
      ofUInt32 S6,
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2432 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2432 (by omega)]; omega
  have hbW : (UInt256.ofNat 384 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 384 (by omega)]; omega
  exact round0 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 q rest hcap hq haw hbK hbW hrun hpc hstack hk hw

private theorem step1 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Wt0 Wt1 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2464 + q).toNat = ofUInt32 Kc1)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 416 + q).toNat = dbl (ofUInt32 Wt1)) :
    runLocatedBlock pround1
      { s with
        pc := UInt256.ofNat 1008
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 S0,
      ofUInt32 S1,
      ofUInt32 S2,
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 S4,
      ofUInt32 S5,
      ofUInt32 S6,
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 1104
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 S0,
      ofUInt32 S1,
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 S4,
      ofUInt32 S5,
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2464 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2464 (by omega)]; omega
  have hbW : (UInt256.ofNat 416 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 416 (by omega)]; omega
  exact round1 _ _ _ _ _ _ _ _ _ _ _ _ rest hcap hq rfl hbK hbW hrun rfl rfl hk hw

private theorem step2 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Wt0 Wt1 Wt2 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2496 + q).toNat = ofUInt32 Kc2)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 448 + q).toNat = dbl (ofUInt32 Wt2)) :
    runLocatedBlock pround2
      { s with
        pc := UInt256.ofNat 1104
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 S0,
      ofUInt32 S1,
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 S4,
      ofUInt32 S5,
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 1200
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 S0,
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 S4,
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2496 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2496 (by omega)]; omega
  have hbW : (UInt256.ofNat 448 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 448 (by omega)]; omega
  exact round2 _ _ _ _ _ _ _ _ _ _ _ _ rest hcap hq rfl hbK hbW hrun rfl rfl hk hw

private theorem step3 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Wt0 Wt1 Wt2 Wt3 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2528 + q).toNat = ofUInt32 Kc3)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 480 + q).toNat = dbl (ofUInt32 Wt3)) :
    runLocatedBlock pround3
      { s with
        pc := UInt256.ofNat 1200
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 S0,
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 S4,
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 1296
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2528 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2528 (by omega)]; omega
  have hbW : (UInt256.ofNat 480 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 480 (by omega)]; omega
  exact round3 _ _ _ _ _ _ _ _ _ _ _ _ rest hcap hq rfl hbK hbW hrun rfl rfl hk hw

private theorem step4 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Wt0 Wt1 Wt2 Wt3 Wt4 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2560 + q).toNat = ofUInt32 Kc4)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 512 + q).toNat = dbl (ofUInt32 Wt4)) :
    runLocatedBlock pround4
      { s with
        pc := UInt256.ofNat 1296
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h0 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 1392
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2560 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2560 (by omega)]; omega
  have hbW : (UInt256.ofNat 512 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 512 (by omega)]; omega
  exact round4 _ _ _ _ _ _ _ _ _ _ _ _ rest hcap hq rfl hbK hbW hrun rfl rfl hk hw

private theorem step5 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2592 + q).toNat = ofUInt32 Kc5)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 544 + q).toNat = dbl (ofUInt32 Wt5)) :
    runLocatedBlock pround5
      { s with
        pc := UInt256.ofNat 1392
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h1 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 1488
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2592 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2592 (by omega)]; omega
  have hbW : (UInt256.ofNat 544 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 544 (by omega)]; omega
  exact round5 _ _ _ _ _ _ _ _ _ _ _ _ rest hcap hq rfl hbK hbW hrun rfl rfl hk hw

private theorem step6 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Kc6 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 Wt6 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2624 + q).toNat = ofUInt32 Kc6)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 576 + q).toNat = dbl (ofUInt32 Wt6)) :
    runLocatedBlock pround6
      { s with
        pc := UInt256.ofNat 1488
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h2 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 1584
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2624 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2624 (by omega)]; omega
  have hbW : (UInt256.ofNat 576 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 576 (by omega)]; omega
  exact round6 _ _ _ _ _ _ _ _ _ _ _ _ rest hcap hq rfl hbK hbW hrun rfl rfl hk hw

private theorem step7 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Kc6 Kc7 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 Wt6 Wt7 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat 2656 + q).toNat = ofUInt32 Kc7)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat 608 + q).toNat = dbl (ofUInt32 Wt7)) :
    runLocatedBlock pround7
      { s with
        pc := UInt256.ofNat 1584
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (d3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (h6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (h3 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3),
      ofUInt32 (d6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 1680
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (h7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (h6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (d7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (d6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbK : (UInt256.ofNat 2656 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 2656 (by omega)]; omega
  have hbW : (UInt256.ofNat 608 + q).toNat + 32 ≤ 4480 := by
    rw [hoff 608 (by omega)]; omega
  exact round7 _ _ _ _ _ _ _ _ _ _ _ _ rest hcap hq rfl hbK hbW hrun rfl rfl hk hw

set_option maxHeartbeats 16000000 in
private theorem step8 (s : State) (S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Kc6 Kc7 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 Wt6 Wt7 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + q) (UInt256.ofNat 2048)))
    (hcode : s.executionEnv.code = bytes)
    (hrun : s.halt = .Running) :
    runLocatedBlock pctrl
      { s with
        pc := UInt256.ofNat 1680
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (h7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (h6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (d7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (d6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ q :: rest } =
      some { s with
        pc := UInt256.ofNat 911
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (h7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (h6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (d7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (d6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ (UInt256.ofNat 256 + q) :: rest } :=
  ctrl_continue _ _ _ _ _ _ _ _ _ _ rest hcap hrun rfl hbr hcode rfl rfl

set_option maxHeartbeats 64000000 in
/-- One full iteration of the eight-round loop plus the control tail, in
the "continue" case: the group pointer `q` advances by 256 and control
returns to the loop head at 911.  All inputs are
opaque; the memory reads are `q`-relative hypotheses on the *initial*
state, sound because the round blocks never write memory. -/
theorem iter_continue (s : State)
    (S0 S1 S2 S3 S4 S5 S6 S7 : UInt32)
    (Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Kc6 Kc7 : UInt32)
    (Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 Wt6 Wt7 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + q) (UInt256.ofNat 2048)))
    (hcode : s.executionEnv.code = bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 912)
    (hstack : s.stack =
      [ofUInt32 S0, ofUInt32 S1, ofUInt32 S2, ofUInt32 S3, ofUInt32 S4, ofUInt32 S5, ofUInt32 S6, ofUInt32 S7] ++ q :: rest)
    (hk0 : MachineState.readWord s.memory
      (UInt256.ofNat 2432 + q).toNat = ofUInt32 Kc0)
    (hw0 : MachineState.readWord s.memory
      (UInt256.ofNat 384 + q).toNat = dbl (ofUInt32 Wt0))
    (hk1 : MachineState.readWord s.memory
      (UInt256.ofNat 2464 + q).toNat = ofUInt32 Kc1)
    (hw1 : MachineState.readWord s.memory
      (UInt256.ofNat 416 + q).toNat = dbl (ofUInt32 Wt1))
    (hk2 : MachineState.readWord s.memory
      (UInt256.ofNat 2496 + q).toNat = ofUInt32 Kc2)
    (hw2 : MachineState.readWord s.memory
      (UInt256.ofNat 448 + q).toNat = dbl (ofUInt32 Wt2))
    (hk3 : MachineState.readWord s.memory
      (UInt256.ofNat 2528 + q).toNat = ofUInt32 Kc3)
    (hw3 : MachineState.readWord s.memory
      (UInt256.ofNat 480 + q).toNat = dbl (ofUInt32 Wt3))
    (hk4 : MachineState.readWord s.memory
      (UInt256.ofNat 2560 + q).toNat = ofUInt32 Kc4)
    (hw4 : MachineState.readWord s.memory
      (UInt256.ofNat 512 + q).toNat = dbl (ofUInt32 Wt4))
    (hk5 : MachineState.readWord s.memory
      (UInt256.ofNat 2592 + q).toNat = ofUInt32 Kc5)
    (hw5 : MachineState.readWord s.memory
      (UInt256.ofNat 544 + q).toNat = dbl (ofUInt32 Wt5))
    (hk6 : MachineState.readWord s.memory
      (UInt256.ofNat 2624 + q).toNat = ofUInt32 Kc6)
    (hw6 : MachineState.readWord s.memory
      (UInt256.ofNat 576 + q).toNat = dbl (ofUInt32 Wt6))
    (hk7 : MachineState.readWord s.memory
      (UInt256.ofNat 2656 + q).toNat = ofUInt32 Kc7)
    (hw7 : MachineState.readWord s.memory
      (UInt256.ofNat 608 + q).toNat = dbl (ofUInt32 Wt7)) :
    runLocatedBlock (pround0 ++ pround1 ++ pround2 ++ pround3 ++ pround4 ++ pround5 ++ pround6 ++ pround7 ++ pctrl) s =
      some { s with
        pc := UInt256.ofNat 911
        activeWords := UInt256.ofNat 140
        stack := [ofUInt32 (h7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (h6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (h5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (h4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4),
      ofUInt32 (d7 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6 Kc7 Wt7),
      ofUInt32 (d6 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5 Kc6 Wt6),
      ofUInt32 (d5 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4 Kc5 Wt5),
      ofUInt32 (d4 S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 Kc1 Wt1 Kc2 Wt2 Kc3 Wt3 Kc4 Wt4)] ++ (UInt256.ofNat 256 + q) :: rest } := by
  refine runLocatedBlock_append _ _
    (step0 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Wt0 q rest hcap hq haw hrun hpc hstack hk0 hw0) hrun ?_
  refine runLocatedBlock_append _ _
    (step1 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Wt0 Wt1 q rest hcap hq hrun hk1 hw1) hrun ?_
  refine runLocatedBlock_append _ _
    (step2 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Wt0 Wt1 Wt2 q rest hcap hq hrun hk2 hw2) hrun ?_
  refine runLocatedBlock_append _ _
    (step3 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Wt0 Wt1 Wt2 Wt3 q rest hcap hq hrun hk3 hw3) hrun ?_
  refine runLocatedBlock_append _ _
    (step4 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Wt0 Wt1 Wt2 Wt3 Wt4 q rest hcap hq hrun hk4 hw4) hrun ?_
  refine runLocatedBlock_append _ _
    (step5 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 q rest hcap hq hrun hk5 hw5) hrun ?_
  refine runLocatedBlock_append _ _
    (step6 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Kc6 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 Wt6 q rest hcap hq hrun hk6 hw6) hrun ?_
  refine runLocatedBlock_append _ _
    (step7 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Kc6 Kc7 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 Wt6 Wt7 q rest hcap hq hrun hk7 hw7) hrun ?_
  exact step8 s S0 S1 S2 S3 S4 S5 S6 S7 Kc0 Kc1 Kc2 Kc3 Kc4 Kc5 Kc6 Kc7 Wt0 Wt1 Wt2 Wt3 Wt4 Wt5 Wt6 Wt7 q rest hcap hbr hcode hrun

end Loop
