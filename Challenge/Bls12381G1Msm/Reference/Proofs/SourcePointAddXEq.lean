import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFinitePrefix

set_option warningAsError true

/-! Exact equal-x condition of the finite G1MSM `pointAdd` dispatcher. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddFiniteState (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddRightInfinityState yst out left right

def pointAddFiniteLeftPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory 1568

def pointAddFiniteRightPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory 1600

def pointAddFiniteLeftXHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteLeftPtr yst out left right).toNat

def pointAddFiniteLeftXLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteLeftPtr yst out left right + 32).toNat

def pointAddFiniteRightXHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteRightPtr yst out left right).toNat

def pointAddFiniteRightXLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddFiniteState yst out left right).memory
    (pointAddFiniteRightPtr yst out left right + 32).toNat

def pointAddXEqValue (yst : EvmState) (out left right : U256) : U256 :=
  fpEqValue
    (pointAddFiniteLeftXHi yst out left right)
    (pointAddFiniteLeftXLo yst out left right)
    (pointAddFiniteRightXHi yst out left right)
    (pointAddFiniteRightXLo yst out left right)

def pointAddXEqState1 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddFiniteState yst out left right) 1600 32

def pointAddXEqState2 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState1 yst out left right)
    (pointAddFiniteRightPtr yst out left right + 32).toNat 32

def pointAddXEqState3 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState2 yst out left right) 1600 32

def pointAddXEqState4 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState3 yst out left right)
    (pointAddFiniteRightPtr yst out left right).toNat 32

def pointAddXEqState5 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState4 yst out left right) 1568 32

def pointAddXEqState6 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState5 yst out left right)
    (pointAddFiniteLeftPtr yst out left right + 32).toNat 32

def pointAddXEqState7 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState6 yst out left right) 1568 32

def pointAddXEqState (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddXEqState7 yst out left right)
    (pointAddFiniteLeftPtr yst out left right).toNat 32

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] theorem pointAddXEqState2_memory (yst : EvmState) (out left right : U256) :
    (pointAddXEqState2 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddXEqState2, pointAddXEqState1]

@[simp] theorem pointAddXEqState4_memory (yst : EvmState) (out left right : U256) :
    (pointAddXEqState4 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddXEqState4, pointAddXEqState3]

@[simp] theorem pointAddXEqState6_memory (yst : EvmState) (out left right : U256) :
    (pointAddXEqState6 yst out left right).memory =
      (pointAddFiniteState yst out left right).memory := by
  simp [pointAddXEqState6, pointAddXEqState5]

theorem step_nestedLoadAdd {funs V} (yst : EvmState)
    (slot delta : Nat) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number slot)], .lit (.number delta)]])
      (.vals
        [loadWord yst.memory
          (loadWord yst.memory (BitVec.ofNat 256 slot).toNat +
            BitVec.ofNat 256 delta).toNat]
        (touchMemory
          (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)
          (loadWord yst.memory (BitVec.ofNat 256 slot).toNat +
            BitVec.ofNat 256 delta).toNat 32)) := by
  have hslotLit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.lit (.number slot)) (.vals [BitVec.ofNat 256 slot] yst) := Step.lit
  have hptr : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload [.lit (.number slot)])
      (.vals [loadWord yst.memory (BitVec.ofNat 256 slot).toNat]
        (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)) := by
    have hslotArgs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
        [.lit (.number slot)] (.vals [BitVec.ofNat 256 slot] yst) :=
      Step.argsCons Step.argsNil hslotLit
    exact Step.builtinOk hslotArgs rfl
  have hdeltaLit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.lit (.number delta)) (.vals [BitVec.ofNat 256 delta] yst) := Step.lit
  have hadd : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .add
        [.builtin .mload [.lit (.number slot)], .lit (.number delta)])
      (.vals
        [loadWord yst.memory (BitVec.ofNat 256 slot).toNat +
          BitVec.ofNat 256 delta]
        (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)) := by
    have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
        [.builtin .mload [.lit (.number slot)], .lit (.number delta)]
        (.vals [loadWord yst.memory (BitVec.ofNat 256 slot).toNat,
          BitVec.ofNat 256 delta]
          (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)) :=
      Step.argsCons (Step.argsCons Step.argsNil hdeltaLit) hptr
    exact Step.builtinOk hargs rfl
  have hloadArgs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
      [.builtin .add
        [.builtin .mload [.lit (.number slot)], .lit (.number delta)]]
      (.vals
        [loadWord yst.memory (BitVec.ofNat 256 slot).toNat +
          BitVec.ofNat 256 delta]
        (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)) :=
    Step.argsCons Step.argsNil hadd
  have hraw : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number slot)], .lit (.number delta)]])
      (.vals
        [loadWord (touchMemory yst (BitVec.ofNat 256 slot).toNat 32).memory
          (loadWord yst.memory (BitVec.ofNat 256 slot).toNat +
            BitVec.ofNat 256 delta).toNat]
        (touchMemory
          (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)
          (loadWord yst.memory (BitVec.ofNat 256 slot).toNat +
            BitVec.ofNat 256 delta).toNat 32)) :=
    Step.builtinOk hloadArgs rfl
  simpa only [touchMemory_memory] using hraw

theorem step_nestedLoad {funs V} (yst : EvmState)
    (slot : Nat) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload [.builtin .mload [.lit (.number slot)]])
      (.vals
        [loadWord yst.memory
          (loadWord yst.memory (BitVec.ofNat 256 slot).toNat).toNat]
        (touchMemory
          (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)
          (loadWord yst.memory (BitVec.ofNat 256 slot).toNat).toNat 32)) := by
  have hslotLit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.lit (.number slot)) (.vals [BitVec.ofNat 256 slot] yst) := Step.lit
  have hptr : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.builtin .mload [.lit (.number slot)])
      (.vals [loadWord yst.memory (BitVec.ofNat 256 slot).toNat]
        (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)) := by
    have hslotArgs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
        [.lit (.number slot)] (.vals [BitVec.ofNat 256 slot] yst) :=
      Step.argsCons Step.argsNil hslotLit
    exact Step.builtinOk hslotArgs rfl
  have hloadArgs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst
      [.builtin .mload [.lit (.number slot)]]
      (.vals [loadWord yst.memory (BitVec.ofNat 256 slot).toNat]
        (touchMemory yst (BitVec.ofNat 256 slot).toNat 32)) :=
    Step.argsCons Step.argsNil hptr
  exact Step.builtinOk hloadArgs rfl

theorem step_pointAddXEqRightLo (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddFiniteState yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]])
      (.vals [pointAddFiniteRightXLo yst out left right]
        (pointAddXEqState2 yst out left right)) := by
  simpa [pointAddFiniteRightXLo, pointAddFiniteRightPtr,
    pointAddXEqState1, pointAddXEqState2] using
    (step_nestedLoadAdd (V := pointAddInitialEnv out left right)
      (pointAddFiniteState yst out left right) 1600 32)

theorem step_pointAddXEqRightHi (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState2 yst out left right)
      (.builtin .mload [.builtin .mload [.lit (.number 1600)]])
      (.vals [pointAddFiniteRightXHi yst out left right]
        (pointAddXEqState4 yst out left right)) := by
  simpa [pointAddFiniteRightXHi, pointAddFiniteRightPtr,
    pointAddXEqState3, pointAddXEqState4] using
    (step_nestedLoad (V := pointAddInitialEnv out left right)
      (pointAddXEqState2 yst out left right) 1600)

theorem step_pointAddXEqLeftLo (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState4 yst out left right)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])
      (.vals [pointAddFiniteLeftXLo yst out left right]
        (pointAddXEqState6 yst out left right)) := by
  simpa [pointAddFiniteLeftXLo, pointAddFiniteLeftPtr,
    pointAddXEqState5, pointAddXEqState6] using
    (step_nestedLoadAdd (V := pointAddInitialEnv out left right)
      (pointAddXEqState4 yst out left right) 1568 32)

theorem step_pointAddXEqLeftHi (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState6 yst out left right)
      (.builtin .mload [.builtin .mload [.lit (.number 1568)]])
      (.vals [pointAddFiniteLeftXHi yst out left right]
        (pointAddXEqState yst out left right)) := by
  simpa [pointAddFiniteLeftXHi, pointAddFiniteLeftPtr,
    pointAddXEqState7, pointAddXEqState] using
    (step_nestedLoad (V := pointAddInitialEnv out left right)
      (pointAddXEqState6 yst out left right) 1568)

theorem step_pointAddXEq (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddFiniteState yst out left right) pointAddXEqCondition
      (.vals [pointAddXEqValue yst out left right]
        (pointAddXEqState yst out left right)) := by
  let V := pointAddInitialEnv out left right
  have hrightLo := step_pointAddXEqRightLo yst out left right
  have hrightHi := step_pointAddXEqRightHi yst out left right
  have hleftLo := step_pointAddXEqLeftLo yst out left right
  have hleftHi := step_pointAddXEqLeftHi yst out left right
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns V (pointAddFiniteState yst out left right)
      [.builtin .mload [.builtin .mload [.lit (.number 1568)]],
       .builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]],
       .builtin .mload [.builtin .mload [.lit (.number 1600)]],
       .builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]]]
      (.vals [pointAddFiniteLeftXHi yst out left right,
        pointAddFiniteLeftXLo yst out left right,
        pointAddFiniteRightXHi yst out left right,
        pointAddFiniteRightXLo yst out left right]
        (pointAddXEqState yst out left right)) :=
    Step.argsCons
      (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hrightLo)
        hrightHi) hleftLo) hleftHi
  rw [pointAddXEqCondition_eq]
  exact step_fpEq_of_args _ _ _ _ hargs (by rfl)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
