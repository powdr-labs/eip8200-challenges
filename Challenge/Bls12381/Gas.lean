import EvmSemantics.EVM.Precompile

set_option warningAsError true

/-!
# EIP-2537 gas schedules

This is the shared, executable gas oracle for the seven BLS12-381
precompiles.  It follows the final EIP-2537 schedule and has no dependency on
an individual challenge.  The G2 table is intentionally stated here instead
of delegated to the pinned dispatcher: that revision is missing repeated
entries beginning at `k = 99` and disagrees with the official vectors for 21
sizes.
-/

namespace Challenge.Bls12381.Gas

open EvmSemantics.EVM

inductive Operation where
  | g1Add
  | g1Msm
  | g2Add
  | g2Msm
  | pairing
  | mapFpToG1
  | mapFp2ToG2
deriving DecidableEq, Repr

/-- Final EIP-2537 G2MSM discounts, indexed by `k - 1`. -/
def g2MsmDiscount : Array Nat :=
  #[1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
    711, 704, 699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
    643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
    606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
    580, 579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
    561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
    546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
    534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524]

def g2MsmCost (input : ByteArray) : Nat :=
  Precompile.blsMsmGas 22500 g2MsmDiscount (input.size / 288)

def precompileCost : Operation → ByteArray → Nat
  | .g1Add, _ => Precompile.blsG1AddGas
  | .g1Msm, input => Precompile.blsG1MsmGas input
  | .g2Add, _ => Precompile.blsG2AddGas
  | .g2Msm, input => g2MsmCost input
  | .pairing, input => Precompile.blsPairingGas input
  | .mapFpToG1, _ => Precompile.blsMapFpToG1Gas
  | .mapFp2ToG2, _ => Precompile.blsMapFp2ToG2Gas

@[simp] theorem g1Add_cost (input : ByteArray) :
    precompileCost .g1Add input = 375 := rfl

@[simp] theorem g2Add_cost (input : ByteArray) :
    precompileCost .g2Add input = 600 := rfl

@[simp] theorem pairing_cost (input : ByteArray) :
    precompileCost .pairing input = 37700 + 32600 * (input.size / 384) := rfl

@[simp] theorem mapFpToG1_cost (input : ByteArray) :
    precompileCost .mapFpToG1 input = 5500 := rfl

@[simp] theorem mapFp2ToG2_cost (input : ByteArray) :
    precompileCost .mapFp2ToG2 input = 23800 := rfl

end Challenge.Bls12381.Gas
