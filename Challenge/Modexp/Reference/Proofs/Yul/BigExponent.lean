import Challenge.Modexp.Reference.Proofs.Yul.BigFold
import Challenge.Modexp.Reference.Proofs.Yul.BigMath
import Challenge.Modexp.Reference.Proofs.Yul.BigPath
import Challenge.Modexp.Reference.Proofs.Yul.WordMath

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Mathematical exponentiation invariants for the direct Yul big path

This module interprets the exact `BigPath` square/copy/multiply/select states.
It is conditional on the fixed-region `BigMath.Represents` contracts and is
independent of the source execution derivation.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open Challenge.YulProof.EvmState
open BigMath

theorem baseBit_toNat (word : U256) (j : Nat) (hj : j < 8) :
    (BigPath.baseBit word j).toNat = BigFold.msbBit word.toNat j := by
  have hj256 : j < 2 ^ 256 := by omega
  have hshift : (7 - BitVec.ofNat 256 j).toNat = 7 - j := by
    rw [BitVec.toNat_sub_of_le]
    · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj256,
        Nat.mod_eq_of_lt (by omega : j < 2 ^ 256)]
      omega
    · simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj256]
      omega
  rw [BigPath.baseBit, BitVec.toNat_and, BitVec.toNat_ushiftRight, hshift]
  change (word.toNat >>> (7 - j)) &&& 1 = _
  rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rfl

theorem baseBit_toNat_le_one (word : U256) (j : Nat) (hj : j < 8) :
    (BigPath.baseBit word j).toNat ≤ 1 := by
  rw [baseBit_toNat word j hj]
  have := BigFold.msbBit_lt_two word.toNat j
  omega

theorem selectLimbPrefix_zero_memory (st : EvmState) (count : Nat)
    (hcount : count ≤ 32) :
    (BigPath.selectLimbPrefix 0 count st).memory =
      (copyWordsState st 2048 2048 count).memory := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigPath.selectLimbPrefix, copyWordsState_succ]
      simp only [BigPath.selectLimbStep, copyWordAt]
      simp only [storeWordAt, YulSemantics.EVM.touchMemory]
      rw [ih (by omega)]
      have hdst : 2048 + BitVec.ofNat 256 count * 32 =
          wordOffset 2048 count := by
        apply BitVec.eq_of_toNat_eq
        simp [wordOffset, BitVec.toNat_add, BitVec.toNat_mul]
        omega
      rw [hdst]
      simp

theorem selectLimbPrefix_one_memory (st : EvmState) (count : Nat)
    (hcount : count ≤ 32) :
    (BigPath.selectLimbPrefix (0 - (1 : U256)) count st).memory =
      (copyWordsState st 2048 3072 count).memory := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BigPath.selectLimbPrefix, copyWordsState_succ]
      simp only [BigPath.selectLimbStep, copyWordAt]
      simp only [storeWordAt, YulSemantics.EVM.touchMemory]
      rw [ih (by omega)]
      have hdst : 2048 + BitVec.ofNat 256 count * 32 =
          wordOffset 2048 count := by
        apply BitVec.eq_of_toNat_eq
        simp [wordOffset, BitVec.toNat_add, BitVec.toNat_mul]
        omega
      have hsrc : 3072 + BitVec.ofNat 256 count * 32 =
          wordOffset 3072 count := by
        apply BitVec.eq_of_toNat_eq
        simp [wordOffset, BitVec.toNat_add, BitVec.toNat_mul]
        omega
      rw [hdst, hsrc]
      congr 1
      exact WordMath.select_one _ _

theorem memoryLimbs_storeWordAt_same (st : EvmState)
    (ptr count index : Nat) (hindex : index < count)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    memoryLimbs
      (storeWordAt st (BitVec.ofNat 256 (ptr + 32 * index))
        (loadWord st.memory (ptr + 32 * index))).memory ptr count =
      memoryLimbs st.memory ptr count := by
  unfold memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hj' : j < count := by simpa using hj
  by_cases heq : j = index
  · subst j
    have haddr : (BitVec.ofNat 256 (ptr + 32 * index)).toNat =
        ptr + 32 * index := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hload := loadWord_storeWordAt st
      (BitVec.ofNat 256 (ptr + 32 * index))
      (loadWord st.memory (ptr + 32 * index))
    rw [haddr] at hload
    exact congrArg BitVec.toNat hload
  · change BitVec.toNat
      (loadWord
        (storeWordAt st (BitVec.ofNat 256 (ptr + 32 * index))
          (loadWord st.memory (ptr + 32 * index))).memory
        (ptr + 32 * j)) = _
    unfold storeWordAt
    rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rcases Nat.lt_or_gt_of_ne heq with hbefore | hafter
    · right; omega
    · left; omega

theorem copyWordsState_self_preserves (st : EvmState)
    (ptr total steps value : Nat) (hsteps : steps ≤ total)
    (hfit : ptr + 32 * total < 2 ^ 256)
    (hrep : Represents st.memory ptr total value) :
    Represents
      (copyWordsState st (BitVec.ofNat 256 ptr) (BitVec.ofNat 256 ptr)
        steps).memory ptr total value := by
  induction steps with
  | zero => simpa [copyWordsState] using hrep
  | succ steps ih =>
      let before := copyWordsState st (BitVec.ofNat 256 ptr)
        (BitVec.ofNat 256 ptr) steps
      have hbefore : Represents before.memory ptr total value := by
        simpa only [before] using ih (by omega)
      have haddr : wordOffset (BitVec.ofNat 256 ptr) steps =
          BitVec.ofNat 256 (ptr + 32 * steps) := by
        apply BitVec.eq_of_toNat_eq
        rw [wordOffset_ofNat ptr steps (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      rw [copyWordsState_succ, copyWordAt, haddr]
      refine ⟨hbefore.1, ?_⟩
      let loaded := touchMemory before (ptr + 32 * steps) 32
      have hsame := memoryLimbs_storeWordAt_same loaded ptr total steps
        (by omega) hfit
      have hloaded : loaded.memory = before.memory := rfl
      simpa only [loaded, hloaded, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : ptr + 32 * steps < 2 ^ 256)] using
        hsame.trans hbefore.2

theorem selectLimbPrefix_represents (st : EvmState) (word : U256)
    (j count square product : Nat) (hj : j < 8) (hcount : count ≤ 32)
    (hsquare : Represents st.memory 2048 count square)
    (hproduct : Represents st.memory 3072 count product) :
    let bit := (BigPath.baseBit word j).toNat
    let after := BigPath.selectLimbPrefix (0 - BigPath.baseBit word j)
      count st
    Represents after.memory 2048 count
      (if bit = 0 then square else product) := by
  let bit := (BigPath.baseBit word j).toNat
  have hbitLe : bit ≤ 1 := baseBit_toNat_le_one word j hj
  have hword : BigPath.baseBit word j = BitVec.ofNat 256 bit :=
    (BitVec.eq_of_toNat_eq (by simp [bit])).symm
  interval_cases bit
  · rw [hword]
    simp only [BitVec.toNat_zero, if_true]
    change Represents (BigPath.selectLimbPrefix 0 count st).memory
      2048 count square
    rw [selectLimbPrefix_zero_memory st count hcount]
    exact copyWordsState_self_preserves st 2048 count count square
      (by omega) (by omega) hsquare
  · rw [hword]
    simp only [show BitVec.ofNat 256 1 = (1 : U256) by rfl,
      BitVec.toNat_one, if_false, Bool.false_eq_true]
    rw [selectLimbPrefix_one_memory st count hcount]
    exact copyWordsState_represents st 2048 3072 count product
      (by omega) (by omega) (by left; omega) hproduct

theorem selectLimbPrefix_preserves (st : EvmState) (word : U256)
    (j count ptr value : Nat) (hj : j < 8) (hcount : count ≤ 32)
    (hptr : 2048 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 2048)
    (hrep : Represents st.memory ptr count value) :
    Represents
      (BigPath.selectLimbPrefix (0 - BigPath.baseBit word j) count st).memory
      ptr count value := by
  let bit := (BigPath.baseBit word j).toNat
  have hbitLe : bit ≤ 1 := baseBit_toNat_le_one word j hj
  have hword : BigPath.baseBit word j = BitVec.ofNat 256 bit :=
    (BitVec.eq_of_toNat_eq (by simp [bit])).symm
  interval_cases bit
  · rw [hword]
    change Represents (BigPath.selectLimbPrefix 0 count st).memory
      ptr count value
    rw [selectLimbPrefix_zero_memory st count hcount]
    exact copyWordsState_preserves st 2048 2048 ptr count value
      (by omega) hptr hrep
  · rw [hword]
    rw [show BitVec.ofNat 256 1 = (1 : U256) by rfl,
      selectLimbPrefix_one_memory st count hcount]
    exact copyWordsState_preserves st 2048 3072 ptr count value
      (by omega) hptr hrep

theorem mulModBigState_preserves (st : EvmState) (a b : U256)
    (count ptr value : Nat) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : 5120 + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ 5120)
    (hrep : Represents st.memory ptr count value) :
    Represents
      (BigMul.mulModBigState st a b 3072 0
        (BitVec.ofNat 256 count)).memory ptr count value := by
  let cleared := clearWordsState st 3072 count
  let copied := copyWordsState cleared 4096 a count
  have hcleared : Represents cleared.memory ptr count value := by
    exact clearWordsState_preserves st 3072 ptr count value (by omega)
      hptrOut hrep
  have hcopied : Represents copied.memory ptr count value := by
    have ha : BitVec.ofNat 256 a.toNat = a :=
      BitVec.eq_of_toNat_eq (by simp)
    have h4096 : (4096 : U256) = BitVec.ofNat 256 4096 := by rfl
    simpa only [copied, ha, h4096] using
      copyWordsState_preserves cleared 4096 a.toNat ptr count value
        (by omega) hptrAddend hcleared
  have hprogress := mulLimbPrefix_preserves copied b count count ptr value
    hcount hptrOut hptrAddend hptrCandidate hcopied
  have hn : (BitVec.ofNat 256 count).toNat = count := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
  simpa only [BigMul.mulModBigState, hn, cleared, copied] using hprogress

theorem exponentBitStep_represents (st : EvmState) (word : U256)
    (j count acc base modulus : Nat) (hj : j < 8) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Represents st.memory 2048 count acc)
    (hbase : Represents st.memory 1024 count base)
    (hmodulus : Represents st.memory 0 count modulus) :
    let after := BigPath.exponentBitStep (BitVec.ofNat 256 count) word j st
    Represents after.memory 2048 count
        (BigFold.powBitStep modulus word.toNat j acc base) ∧
      Represents after.memory 1024 count base ∧
      Represents after.memory 0 count modulus := by
  let squareValue := (acc * acc) % modulus
  let productValue := (squareValue * base) % modulus
  let squared := BigMul.mulModBigState st 2048 2048 3072 0
    (BitVec.ofNat 256 count)
  let copied := copyWordsState squared 2048 3072 count
  let product := BigMul.mulModBigState copied 2048 1024 3072 0
    (BitVec.ofNat 256 count)
  have h2048 : (2048 : U256) = BitVec.ofNat 256 2048 := by rfl
  have h1024 : (1024 : U256) = BitVec.ofNat 256 1024 := by rfl
  have hsquared := mulModBigState_represents st 2048 count acc acc modulus
    hcount (by omega) hmodulusPos hacc hacc hmodulus haccReduced
  have hsquaredOut : Represents squared.memory 3072 count squareValue := by
    simpa only [squared, squareValue, h2048] using hsquared.1
  have hsquaredBase : Represents squared.memory 1024 count base := by
    exact mulModBigState_preserves st 2048 2048 count 1024 base hcount
      (by right; omega) (by right; omega) (by right; omega) hbase
  have hsquaredModulus : Represents squared.memory 0 count modulus := by
    simpa only [squared, h2048] using hsquared.2.2.2
  have hcopiedSquare : Represents copied.memory 2048 count squareValue := by
    exact copyWordsState_represents squared 2048 3072 count squareValue
      (by omega) (by omega) (by left; omega) hsquaredOut
  have hcopiedBase : Represents copied.memory 1024 count base := by
    exact copyWordsState_preserves squared 2048 3072 1024 count base
      (by omega) (by right; omega) hsquaredBase
  have hcopiedModulus : Represents copied.memory 0 count modulus := by
    exact copyWordsState_preserves squared 2048 3072 0 count modulus
      (by omega) (by right; omega) hsquaredModulus
  have hsquareReduced : squareValue < modulus :=
    Nat.mod_lt _ hmodulusPos
  have hproductState := mulModBigState_represents copied 1024 count
    squareValue base modulus hcount (by omega) hmodulusPos hcopiedSquare
    hcopiedBase hcopiedModulus hsquareReduced
  have hproduct : Represents product.memory 3072 count productValue := by
    simpa only [product, productValue, h1024] using hproductState.1
  have hproductSquare : Represents product.memory 2048 count squareValue := by
    simpa only [product, h1024] using hproductState.2.1
  have hproductBase : Represents product.memory 1024 count base := by
    simpa only [product, h1024] using hproductState.2.2.1
  have hproductModulus : Represents product.memory 0 count modulus := by
    simpa only [product, h1024] using hproductState.2.2.2
  have hselected := selectLimbPrefix_represents product word j count
    squareValue productValue hj hcount hproductSquare hproduct
  have hselectedBase := selectLimbPrefix_preserves product word j count
    1024 base hj hcount (by right; omega) hproductBase
  have hselectedModulus := selectLimbPrefix_preserves product word j count
    0 modulus hj hcount (by right; omega) hproductModulus
  have hn : (BitVec.ofNat 256 count).toNat = count := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
  have hvalue :
      (if (BigPath.baseBit word j).toNat = 0 then squareValue
        else productValue) =
      BigFold.powBitStep modulus word.toNat j acc base := by
    rw [baseBit_toNat word j hj]
    rfl
  have hselected' : Represents
      (BigPath.selectLimbPrefix (0 - BigPath.baseBit word j) count
        product).memory 2048 count
      (BigFold.powBitStep modulus word.toNat j acc base) := by
    rw [← hvalue]
    exact hselected
  simpa only [BigPath.exponentBitStep, hn, squared, copied, product] using
    And.intro hselected' (And.intro hselectedBase hselectedModulus)

theorem exponentBitPrefix_represents (st : EvmState) (word : U256)
    (steps count acc base modulus : Nat) (hsteps : steps ≤ 8)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Represents st.memory 2048 count acc)
    (hbase : Represents st.memory 1024 count base)
    (hmodulus : Represents st.memory 0 count modulus) :
    let after := BigPath.exponentBitPrefix (BitVec.ofNat 256 count) word
      steps st
    let value := BigFold.powBitAfter modulus word.toNat base steps acc
    Represents after.memory 2048 count value ∧
      Represents after.memory 1024 count base ∧
      Represents after.memory 0 count modulus := by
  induction steps with
  | zero =>
      simpa [BigPath.exponentBitPrefix, BigFold.powBitAfter] using
        And.intro hacc (And.intro hbase hmodulus)
  | succ steps ih =>
      have hsteps' : steps ≤ 8 := by omega
      let before := BigPath.exponentBitPrefix (BitVec.ofNat 256 count) word
        steps st
      let beforeValue := BigFold.powBitAfter modulus word.toNat base steps acc
      have hbefore := ih hsteps'
      have hbeforeReduced := BigFold.powBitAfter_lt modulus word.toNat base
        steps acc hmodulusPos haccReduced
      have hstep := exponentBitStep_represents before word steps count
        beforeValue base modulus (by omega) hcount hmodulusPos hbeforeReduced
        hbefore.1 hbefore.2.1 hbefore.2.2
      simpa [BigPath.exponentBitPrefix, BigFold.powBitAfter, before,
        beforeValue] using hstep

@[simp] theorem clearWordsState_env (st : EvmState) (ptr : U256)
    (count : Nat) : (clearWordsState st ptr count).env = st.env := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [clearWordsState, storeWordAt, YulSemantics.EVM.touchMemory, ih]

@[simp] theorem copyWordsState_env (st : EvmState) (dst src : U256)
    (count : Nat) : (copyWordsState st dst src count).env = st.env := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [copyWordsState, copyWordAt, storeWordAt,
        YulSemantics.EVM.touchMemory, ih]

@[simp] theorem addPhase_env (st : EvmState) (dst src mask : U256)
    (count : Nat) :
    (BigArithmetic.addPhase st dst src mask count).state.env = st.env := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [BigArithmetic.addPhase, BigArithmetic.addStep, storeWordAt,
        YulSemantics.EVM.touchMemory, ih]

@[simp] theorem subPhase_env (st : EvmState) (dst modulus : U256)
    (count : Nat) :
    (BigArithmetic.subPhase st dst modulus count).state.env = st.env := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [BigArithmetic.subPhase, BigArithmetic.subStep, storeWordAt,
        YulSemantics.EVM.touchMemory, ih]

@[simp] theorem selectPhase_env (st : EvmState) (dst mask : U256)
    (count : Nat) :
    (BigArithmetic.selectPhase st dst mask count).env = st.env := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [BigArithmetic.selectPhase, BigArithmetic.selectStep, storeWordAt,
        YulSemantics.EVM.touchMemory, ih]

@[simp] theorem addMaskedModState_env (st : EvmState)
    (dst src take modulus : U256) (count : Nat) :
    (BigArithmetic.addMaskedModState st dst src take modulus count).env =
      st.env := by
  simp [BigArithmetic.addMaskedModState]

@[simp] theorem mulBitPrefix_env (st : EvmState)
    (out modulus n word : U256) (steps : Nat) :
    (BigMul.mulBitPrefix out modulus n word steps st).env = st.env := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigMul.mulBitPrefix, BigMul.mulBitStep, ih]

@[simp] theorem mulLimbPrefix_env (st : EvmState)
    (b out modulus n : U256) (steps : Nat) :
    (BigMul.mulLimbPrefix b out modulus n steps st).env = st.env := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigMul.mulLimbPrefix, BigMul.mulLimbStep,
        YulSemantics.EVM.touchMemory, ih]

@[simp] theorem mulModBigState_env (st : EvmState)
    (a b out modulus n : U256) :
    (BigMul.mulModBigState st a b out modulus n).env = st.env := by
  simp [BigMul.mulModBigState]

@[simp] theorem selectLimbPrefix_env (st : EvmState) (mask : U256)
    (steps : Nat) : (BigPath.selectLimbPrefix mask steps st).env = st.env := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigPath.selectLimbPrefix, BigPath.selectLimbStep, storeWordAt,
        YulSemantics.EVM.touchMemory, ih]

@[simp] theorem exponentBitPrefix_env (st : EvmState) (n word : U256)
    (steps : Nat) :
    (BigPath.exponentBitPrefix n word steps st).env = st.env := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigPath.exponentBitPrefix, BigPath.exponentBitStep, ih]

@[simp] theorem exponentBytePrefix_env (st : EvmState) (expOff n : U256)
    (steps : Nat) :
    (BigPath.exponentBytePrefix expOff n steps st).env = st.env := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [BigPath.exponentBytePrefix, BigPath.exponentByteStep, ih]

theorem exponentBytePrefix_represents (st : EvmState) (input : ByteArray)
    (expOffset steps count acc base modulus : Nat)
    (hbound : expOffset + steps < 2 ^ 256)
    (hcalldata : st.env.calldata = input.toList)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Represents st.memory 2048 count acc)
    (hbase : Represents st.memory 1024 count base)
    (hmodulus : Represents st.memory 0 count modulus) :
    let after := BigPath.exponentBytePrefix (BitVec.ofNat 256 expOffset)
      (BitVec.ofNat 256 count) steps st
    let value := BigFold.exponentByteAfter input expOffset modulus base
      steps acc
    Represents after.memory 2048 count value ∧
      Represents after.memory 1024 count base ∧
      Represents after.memory 0 count modulus := by
  induction steps with
  | zero =>
      simpa [BigPath.exponentBytePrefix, BigFold.exponentByteAfter] using
        And.intro hacc (And.intro hbase hmodulus)
  | succ steps ih =>
      have hbound' : expOffset + steps < 2 ^ 256 := by omega
      let before := BigPath.exponentBytePrefix (BitVec.ofNat 256 expOffset)
        (BitVec.ofNat 256 count) steps st
      let word := StateModel.calldataByteValue before
        (BitVec.ofNat 256 expOffset + BitVec.ofNat 256 steps)
      let beforeValue := BigFold.exponentByteAfter input expOffset modulus base
        steps acc
      have hbefore := ih hbound'
      have hbeforeReduced := BigFold.exponentByteAfter_lt input expOffset
        modulus base steps acc hmodulusPos haccReduced
      have hcalldataBefore : before.env.calldata = input.toList := by
        rw [exponentBytePrefix_env]
        exact hcalldata
      have hoff :
          (BitVec.ofNat 256 expOffset + BitVec.ofNat 256 steps).toNat =
            expOffset + steps := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : expOffset < 2 ^ 256),
          Nat.mod_eq_of_lt (by omega : steps < 2 ^ 256),
          Nat.mod_eq_of_lt hbound']
      have hwordNat : word.toNat =
          (byteFrom input.toList (expOffset + steps)).toNat := by
        dsimp only [word]
        rw [WordMath.calldataByteValue_toNat before input _
          hcalldataBefore, hoff]
      have hwordByte : word.toNat < 256 := by
        rw [hwordNat]
        exact (byteFrom input.toList (expOffset + steps)).toNat_lt
      have hbits := exponentBitPrefix_represents before word 8 count
        beforeValue base modulus (by omega) hcount hmodulusPos
        hbeforeReduced hbefore.1 hbefore.2.1 hbefore.2.2
      have hfold := BigFold.powBitAfter_eight modulus word.toNat base
        beforeValue hbeforeReduced hwordByte
      have hvalue : BigFold.powBitAfter modulus word.toNat base 8
          beforeValue =
          BigFold.exponentByteAfter input expOffset modulus base
            (steps + 1) acc := by
        rw [hfold, BigFold.exponentByteAfter, hwordNat]
      simpa [BigPath.exponentBytePrefix, BigPath.exponentByteStep, before,
        word, beforeValue, hvalue] using hbits

/-- The challenge-layout exponent fold, conditional on the mathematical
invariants of `initializedAccumulatorState`. -/
theorem exponentiatedState_represents (st : EvmState) (input : ByteArray)
    (bsize esize modulusSize modulusOffset count baseNat modulusNat : Nat)
    (hbound : 96 + bsize + esize < 2 ^ 256)
    (hcount : count ≤ 32)
    (hn : (BigPath.limbCount (BitVec.ofNat 256 modulusSize)).toNat = count)
    (hmodulusPos : 0 < modulusNat)
    (hcalldata :
      (BigPath.initializedAccumulatorState st (BitVec.ofNat 256 bsize)
        (BitVec.ofNat 256 modulusSize) 96
        (BitVec.ofNat 256 modulusOffset)).env.calldata = input.toList)
    (hacc : Represents
      (BigPath.initializedAccumulatorState st (BitVec.ofNat 256 bsize)
        (BitVec.ofNat 256 modulusSize) 96
        (BitVec.ofNat 256 modulusOffset)).memory
      2048 count (1 % modulusNat))
    (hbase : Represents
      (BigPath.initializedAccumulatorState st (BitVec.ofNat 256 bsize)
        (BitVec.ofNat 256 modulusSize) 96
        (BitVec.ofNat 256 modulusOffset)).memory
      1024 count (baseNat % modulusNat))
    (hmodulus : Represents
      (BigPath.initializedAccumulatorState st (BitVec.ofNat 256 bsize)
        (BitVec.ofNat 256 modulusSize) 96
        (BitVec.ofNat 256 modulusOffset)).memory
      0 count modulusNat) :
    let after := BigPath.exponentiatedState st
      (BitVec.ofNat 256 bsize) (BitVec.ofNat 256 esize)
      (BitVec.ofNat 256 modulusSize) 96
      (BitVec.ofNat 256 (96 + bsize)) (BitVec.ofNat 256 modulusOffset)
    Represents after.memory 2048 count
        (Precompile.modPow baseNat
          (Precompile.bytesToNatPadded input (96 + bsize) esize) modulusNat) ∧
      Represents after.memory 1024 count (baseNat % modulusNat) ∧
      Represents after.memory 0 count modulusNat := by
  let initial := BigPath.initializedAccumulatorState st
    (BitVec.ofNat 256 bsize) (BitVec.ofNat 256 modulusSize) 96
    (BitVec.ofNat 256 modulusOffset)
  have hrun := exponentBytePrefix_represents initial input (96 + bsize)
    esize count (1 % modulusNat) (baseNat % modulusNat) modulusNat hbound
    hcalldata hcount hmodulusPos (Nat.mod_lt _ hmodulusPos) hacc hbase
    hmodulus
  have hvalue := BigFold.exponentByteAfter_eq_modPow input (96 + bsize)
    baseNat modulusNat esize hmodulusPos
  have hesize : (BitVec.ofNat 256 esize).toNat = esize := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnWord : BigPath.limbCount (BitVec.ofNat 256 modulusSize) =
      BitVec.ofNat 256 count := by
    apply BitVec.eq_of_toNat_eq
    rw [hn, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hcount.trans_lt (by norm_num : 32 < 2 ^ 256))]
  have hrun' :
      Represents
        (BigPath.exponentBytePrefix (BitVec.ofNat 256 (96 + bsize))
          (BitVec.ofNat 256 count) esize initial).memory
        2048 count
        (Precompile.modPow baseNat
          (Precompile.bytesToNatPadded input (96 + bsize) esize) modulusNat) ∧
      Represents
        (BigPath.exponentBytePrefix (BitVec.ofNat 256 (96 + bsize))
          (BitVec.ofNat 256 count) esize initial).memory
        1024 count (baseNat % modulusNat) ∧
      Represents
        (BigPath.exponentBytePrefix (BitVec.ofNat 256 (96 + bsize))
          (BitVec.ofNat 256 count) esize initial).memory
        0 count modulusNat := by
    rw [← hvalue]
    exact hrun
  simpa only [BigPath.exponentiatedState, hnWord, hesize, initial] using hrun'

end Challenge.Modexp.Reference.Proofs.Yul.BigExponent
