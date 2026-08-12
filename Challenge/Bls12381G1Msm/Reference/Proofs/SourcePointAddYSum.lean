import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddXEq

set_option warningAsError true

/-! Relational execution of the equal-x branch's Y-coordinate sum. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddFiniteLeftYHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteLeftPtr yst out left right + 64).toNat

def pointAddFiniteLeftYLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteLeftPtr yst out left right + 96).toNat

def pointAddFiniteRightYHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteRightPtr yst out left right + 64).toNat

def pointAddFiniteRightYLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteRightPtr yst out left right + 96).toNat

def pointAddYSumState1 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState yst out left right) 1600 32

def pointAddYSumState2 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState1 yst out left right)
    (pointAddFiniteRightPtr yst out left right + 96).toNat 32

def pointAddYSumState3 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState2 yst out left right) 1600 32

def pointAddYSumState4 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState3 yst out left right)
    (pointAddFiniteRightPtr yst out left right + 64).toNat 32

def pointAddYSumState5 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState4 yst out left right) 1568 32

def pointAddYSumState6 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState5 yst out left right)
    (pointAddFiniteLeftPtr yst out left right + 96).toNat 32

def pointAddYSumState7 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState6 yst out left right) 1568 32

def pointAddYSumState (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState7 yst out left right)
    (pointAddFiniteLeftPtr yst out left right + 64).toNat 32

def pointAddYSumResult (yst : EvmState) (out left right : U256) : U256 × U256 :=
  fpAddResult
    (pointAddFiniteLeftYHi yst out left right)
    (pointAddFiniteLeftYLo yst out left right)
    (pointAddFiniteRightYHi yst out left right)
    (pointAddFiniteRightYLo yst out left right)

def pointAddYSumEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00110", "\x00111"].zip
    [(fpAddResult
      (pointAddFiniteLeftYHi yst out left right)
      (pointAddFiniteLeftYLo yst out left right)
      (pointAddFiniteRightYHi yst out left right)
      (pointAddFiniteRightYLo yst out left right)).1,
     (fpAddResult
      (pointAddFiniteLeftYHi yst out left right)
      (pointAddFiniteLeftYLo yst out left right)
      (pointAddFiniteRightYHi yst out left right)
      (pointAddFiniteRightYLo yst out left right)).2] ++ pointAddInitialEnv out left right

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem pointAddXEqState_memory (yst : EvmState) (out left right : U256) :
    (pointAddXEqState yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddXEqState, pointAddXEqState7]

@[simp] private theorem pointAddYSumState2_memory (yst : EvmState) (out left right : U256) :
    (pointAddYSumState2 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddYSumState2, pointAddYSumState1, pointAddXEqState_memory]

@[simp] private theorem pointAddYSumState4_memory (yst : EvmState) (out left right : U256) :
    (pointAddYSumState4 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddYSumState4, pointAddYSumState3, pointAddYSumState2_memory]

@[simp] private theorem pointAddYSumState6_memory (yst : EvmState) (out left right : U256) :
    (pointAddYSumState6 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddYSumState6, pointAddYSumState5, pointAddYSumState4_memory]

private theorem step_pointAddYSumRightLo {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddXEqState yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 96)]])
      (.vals [pointAddFiniteRightYLo yst out left right]
        (pointAddYSumState2 yst out left right)) := by
  simpa [pointAddFiniteRightYLo, pointAddFiniteRightPtr,
    pointAddYSumState1, pointAddYSumState2, pointAddXEqState_memory] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddXEqState yst out left right) 1600 96)

private theorem step_pointAddYSumRightHi {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddYSumState2 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 64)]])
      (.vals [pointAddFiniteRightYHi yst out left right]
        (pointAddYSumState4 yst out left right)) := by
  simpa [pointAddFiniteRightYHi, pointAddFiniteRightPtr,
    pointAddYSumState3, pointAddYSumState4] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddYSumState2 yst out left right) 1600 64)

private theorem step_pointAddYSumLeftLo {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddYSumState4 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])
      (.vals [pointAddFiniteLeftYLo yst out left right]
        (pointAddYSumState6 yst out left right)) := by
  simpa [pointAddFiniteLeftYLo, pointAddFiniteLeftPtr,
    pointAddYSumState5, pointAddYSumState6] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddYSumState4 yst out left right) 1568 96)

private theorem step_pointAddYSumLeftHi {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddYSumState6 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])
      (.vals [pointAddFiniteLeftYHi yst out left right]
        (pointAddYSumState yst out left right)) := by
  simpa [pointAddFiniteLeftYHi, pointAddFiniteLeftPtr,
    pointAddYSumState7, pointAddYSumState] using
    (step_nestedLoadAdd (funs := funs) (V := V)
      (pointAddYSumState6 yst out left right) 1568 64)

theorem step_pointAddYSumArgs {funs V} (yst : EvmState)
    (out left right : U256) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddXEqState yst out left right) pointAddYSumArgs
      (.vals [pointAddFiniteLeftYHi yst out left right,
        pointAddFiniteLeftYLo yst out left right,
        pointAddFiniteRightYHi yst out left right,
        pointAddFiniteRightYLo yst out left right]
        (pointAddYSumState yst out left right)) := by
  have hrightLo := step_pointAddYSumRightLo (funs := funs) (V := V)
    yst out left right
  have hrightHi := step_pointAddYSumRightHi (funs := funs) (V := V)
    yst out left right
  have hleftLo := step_pointAddYSumLeftLo (funs := funs) (V := V)
    yst out left right
  have hleftHi := step_pointAddYSumLeftHi (funs := funs) (V := V)
    yst out left right
  rw [pointAddYSumArgs_eq]
  exact Step.argsCons
    (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hrightLo)
      hrightHi) hleftLo) hleftHi

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
