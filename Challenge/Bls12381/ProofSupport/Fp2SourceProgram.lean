set_option warningAsError true

/-! # Parametric source programs for BLS12-381 Fp2 operations

This module contains no field arithmetic. The same authoritative programs are
interpreted by a pure runtime algebra and by an audit writer algebra downstream.
-/

namespace Challenge.Bls12381.ProofSupport.Fp2.SourceProgram

inductive Ref where
  | a0 | a1 | b0 | b1
  | v0 | v1 | aSum | bSum | cross | vSum | c0 | c1
  | a0Square | a1Square | norm | normInv | negA1
deriving DecidableEq

inductive Event where
  | add (left right output : Ref)
  | sub (left right output : Ref)
  | mul (left right output : Ref)
  | square (input output : Ref)
  | inv (input output : Ref)
  | neg (input output : Ref)
deriving DecidableEq

structure Ops (Wire : Type) (M : Type → Type) [Monad M] (Cell : Type) where
  input : Ref → Wire → Cell
  value : Cell → Wire
  add : Ref → Cell → Cell → M Cell
  sub : Ref → Cell → Cell → M Cell
  mul : Ref → Cell → Cell → M Cell
  square : Ref → Cell → M Cell
  inv : Ref → Cell → M Cell
  neg : Ref → Cell → M Cell

/-- The one authoritative multiplication program. -/
def runMulWith {Wire : Type} {M : Type → Type} [Monad M] {Cell : Type}
    (ops : Ops Wire M Cell) (a0Wire a1Wire b0Wire b1Wire : Wire) :
    M (Cell × Cell) := do
  let a0 := ops.input .a0 a0Wire
  let a1 := ops.input .a1 a1Wire
  let b0 := ops.input .b0 b0Wire
  let b1 := ops.input .b1 b1Wire
  let v0 ← ops.mul .v0 a0 b0
  let v1 ← ops.mul .v1 a1 b1
  let aSum ← ops.add .aSum a0 a1
  let bSum ← ops.add .bSum b0 b1
  let cross ← ops.mul .cross aSum bSum
  let vSum ← ops.add .vSum v0 v1
  let c1 ← ops.sub .c1 cross vSum
  let c0 ← ops.sub .c0 v0 v1
  pure (c0, c1)

/-- The one authoritative inversion program. -/
def runInvWith {Wire : Type} {M : Type → Type} [Monad M] {Cell : Type}
    (ops : Ops Wire M Cell) (a0Wire a1Wire : Wire) : M (Cell × Cell) := do
  let a0 := ops.input .a0 a0Wire
  let a1 := ops.input .a1 a1Wire
  let a0Square ← ops.square .a0Square a0
  let a1Square ← ops.square .a1Square a1
  let norm ← ops.add .norm a0Square a1Square
  let normInv ← ops.inv .normInv norm
  let c0 ← ops.mul .c0 a0 normInv
  let negA1 ← ops.neg .negA1 a1
  let c1 ← ops.mul .c1 negA1 normInv
  pure (c0, c1)

theorem runMulWith_id_eq {Wire Cell : Type} (ops : Ops Wire Id Cell)
    (a0 a1 b0 b1 : Wire) :
    Id.run (runMulWith ops a0 a1 b0 b1) =
      let a0 := ops.input .a0 a0
      let a1 := ops.input .a1 a1
      let b0 := ops.input .b0 b0
      let b1 := ops.input .b1 b1
      let v0 := Id.run (ops.mul .v0 a0 b0)
      let v1 := Id.run (ops.mul .v1 a1 b1)
      let aSum := Id.run (ops.add .aSum a0 a1)
      let bSum := Id.run (ops.add .bSum b0 b1)
      let cross := Id.run (ops.mul .cross aSum bSum)
      let vSum := Id.run (ops.add .vSum v0 v1)
      let c1 := Id.run (ops.sub .c1 cross vSum)
      let c0 := Id.run (ops.sub .c0 v0 v1)
      (c0, c1) := by
  rfl

theorem runInvWith_id_eq {Wire Cell : Type} (ops : Ops Wire Id Cell)
    (a0 a1 : Wire) :
    Id.run (runInvWith ops a0 a1) =
      let a0 := ops.input .a0 a0
      let a1 := ops.input .a1 a1
      let a0Square := Id.run (ops.square .a0Square a0)
      let a1Square := Id.run (ops.square .a1Square a1)
      let norm := Id.run (ops.add .norm a0Square a1Square)
      let normInv := Id.run (ops.inv .normInv norm)
      let c0 := Id.run (ops.mul .c0 a0 normInv)
      let negA1 := Id.run (ops.neg .negA1 a1)
      let c1 := Id.run (ops.mul .c1 negA1 normInv)
      (c0, c1) := by
  rfl

theorem runMulWith_good {Wire Cell : Type} (ops : Ops Wire Id Cell)
    (Good : Cell → Prop)
    (hadd : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.add output a b)))
    (hsub : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.sub output a b)))
    (hmul : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.mul output a b)))
    (a0 a1 b0 b1 : Wire)
    (ha0 : Good (ops.input .a0 a0)) (ha1 : Good (ops.input .a1 a1))
    (hb0 : Good (ops.input .b0 b0)) (hb1 : Good (ops.input .b1 b1)) :
    let result := Id.run (runMulWith ops a0 a1 b0 b1)
    Good result.1 ∧ Good result.2 := by
  rw [runMulWith_id_eq]
  dsimp only
  have hv0 := hmul .v0 _ _ ha0 hb0
  have hv1 := hmul .v1 _ _ ha1 hb1
  have haSum := hadd .aSum _ _ ha0 ha1
  have hbSum := hadd .bSum _ _ hb0 hb1
  have hcross := hmul .cross _ _ haSum hbSum
  have hvSum := hadd .vSum _ _ hv0 hv1
  exact ⟨hsub .c0 _ _ hv0 hv1, hsub .c1 _ _ hcross hvSum⟩

theorem runInvWith_good {Wire Cell : Type} (ops : Ops Wire Id Cell)
    (Good : Cell → Prop)
    (hadd : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.add output a b)))
    (hmul : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.mul output a b)))
    (hsquare : ∀ output a, Good a →
      Good (Id.run (ops.square output a)))
    (hinv : ∀ output a, Good a → Good (Id.run (ops.inv output a)))
    (hneg : ∀ output a, Good a → Good (Id.run (ops.neg output a)))
    (a0 a1 : Wire) (ha0 : Good (ops.input .a0 a0))
    (ha1 : Good (ops.input .a1 a1)) :
    let result := Id.run (runInvWith ops a0 a1)
    Good result.1 ∧ Good result.2 := by
  rw [runInvWith_id_eq]
  dsimp only
  have ha0Square := hsquare .a0Square _ ha0
  have ha1Square := hsquare .a1Square _ ha1
  have hnorm := hadd .norm _ _ ha0Square ha1Square
  have hnormInv := hinv .normInv _ hnorm
  have hnegA1 := hneg .negA1 _ ha1
  exact ⟨hmul .c0 _ _ ha0 hnormInv, hmul .c1 _ _ hnegA1 hnormInv⟩

structure Semantics (Value : Type) where
  add : Value → Value → Value
  sub : Value → Value → Value
  mul : Value → Value → Value
  square : Value → Value
  inv : Value → Value
  neg : Value → Value

theorem runMulWith_refines {Wire Cell Value : Type} (ops : Ops Wire Id Cell)
    (Good : Cell → Prop) (eval : Cell → Value) (spec : Semantics Value)
    (hadd : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.add output a b)) ∧
        eval (Id.run (ops.add output a b)) = spec.add (eval a) (eval b))
    (hsub : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.sub output a b)) ∧
        eval (Id.run (ops.sub output a b)) = spec.sub (eval a) (eval b))
    (hmul : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.mul output a b)) ∧
        eval (Id.run (ops.mul output a b)) = spec.mul (eval a) (eval b))
    (a0 a1 b0 b1 : Wire)
    (ha0 : Good (ops.input .a0 a0)) (ha1 : Good (ops.input .a1 a1))
    (hb0 : Good (ops.input .b0 b0)) (hb1 : Good (ops.input .b1 b1)) :
    let inputA0 := ops.input .a0 a0
    let inputA1 := ops.input .a1 a1
    let inputB0 := ops.input .b0 b0
    let inputB1 := ops.input .b1 b1
    let result := Id.run (runMulWith ops a0 a1 b0 b1)
    Good result.1 ∧ Good result.2 ∧
      eval result.1 = spec.sub
        (spec.mul (eval inputA0) (eval inputB0))
        (spec.mul (eval inputA1) (eval inputB1)) ∧
      eval result.2 = spec.sub
        (spec.mul (spec.add (eval inputA0) (eval inputA1))
          (spec.add (eval inputB0) (eval inputB1)))
        (spec.add (spec.mul (eval inputA0) (eval inputB0))
          (spec.mul (eval inputA1) (eval inputB1))) := by
  rw [runMulWith_id_eq]
  dsimp only
  obtain ⟨hv0, hv0eval⟩ := hmul .v0 _ _ ha0 hb0
  obtain ⟨hv1, hv1eval⟩ := hmul .v1 _ _ ha1 hb1
  obtain ⟨haSum, haSumEval⟩ := hadd .aSum _ _ ha0 ha1
  obtain ⟨hbSum, hbSumEval⟩ := hadd .bSum _ _ hb0 hb1
  obtain ⟨hcross, hcrossEval⟩ := hmul .cross _ _ haSum hbSum
  obtain ⟨hvSum, hvSumEval⟩ := hadd .vSum _ _ hv0 hv1
  obtain ⟨hc1, hc1eval⟩ := hsub .c1 _ _ hcross hvSum
  obtain ⟨hc0, hc0eval⟩ := hsub .c0 _ _ hv0 hv1
  refine ⟨hc0, hc1, ?_, ?_⟩
  · rw [hc0eval, hv0eval, hv1eval]
  · rw [hc1eval, hcrossEval, hvSumEval, haSumEval, hbSumEval,
      hv0eval, hv1eval]

theorem runInvWith_refines {Wire Cell Value : Type} (ops : Ops Wire Id Cell)
    (Good : Cell → Prop) (eval : Cell → Value) (spec : Semantics Value)
    (hadd : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.add output a b)) ∧
        eval (Id.run (ops.add output a b)) = spec.add (eval a) (eval b))
    (hmul : ∀ output a b, Good a → Good b →
      Good (Id.run (ops.mul output a b)) ∧
        eval (Id.run (ops.mul output a b)) = spec.mul (eval a) (eval b))
    (hsquare : ∀ output a, Good a →
      Good (Id.run (ops.square output a)) ∧
        eval (Id.run (ops.square output a)) = spec.square (eval a))
    (hinv : ∀ output a, Good a →
      Good (Id.run (ops.inv output a)) ∧
        eval (Id.run (ops.inv output a)) = spec.inv (eval a))
    (hneg : ∀ output a, Good a →
      Good (Id.run (ops.neg output a)) ∧
        eval (Id.run (ops.neg output a)) = spec.neg (eval a))
    (a0 a1 : Wire) (ha0 : Good (ops.input .a0 a0))
    (ha1 : Good (ops.input .a1 a1)) :
    let inputA0 := ops.input .a0 a0
    let inputA1 := ops.input .a1 a1
    let result := Id.run (runInvWith ops a0 a1)
    let norm := spec.add (spec.square (eval inputA0))
      (spec.square (eval inputA1))
    Good result.1 ∧ Good result.2 ∧
      eval result.1 = spec.mul (eval inputA0) (spec.inv norm) ∧
      eval result.2 = spec.mul (spec.neg (eval inputA1)) (spec.inv norm) := by
  rw [runInvWith_id_eq]
  dsimp only
  obtain ⟨ha0Square, ha0SquareEval⟩ := hsquare .a0Square _ ha0
  obtain ⟨ha1Square, ha1SquareEval⟩ := hsquare .a1Square _ ha1
  obtain ⟨hnorm, hnormEval⟩ := hadd .norm _ _ ha0Square ha1Square
  obtain ⟨hnormInv, hnormInvEval⟩ := hinv .normInv _ hnorm
  obtain ⟨hc0, hc0eval⟩ := hmul .c0 _ _ ha0 hnormInv
  obtain ⟨hnegA1, hnegA1eval⟩ := hneg .negA1 _ ha1
  obtain ⟨hc1, hc1eval⟩ := hmul .c1 _ _ hnegA1 hnormInv
  refine ⟨hc0, hc1, ?_, ?_⟩
  · rw [hc0eval, hnormInvEval, hnormEval, ha0SquareEval, ha1SquareEval]
  · rw [hc1eval, hnegA1eval, hnormInvEval, hnormEval,
      ha0SquareEval, ha1SquareEval]

structure AuditCell (Cell : Type) where
  value : Cell
  ref : Ref

abbrev AuditM := StateM (List Event)

def emit (event : Event) : AuditM Unit := fun events =>
  ((), events ++ [event])

def auditOpsOf {Wire Cell : Type} (base : Ops Wire Id Cell) :
    Ops Wire AuditM (AuditCell Cell) where
  input := fun ref value => ⟨base.input ref value, ref⟩
  value := fun cell => base.value cell.value
  add := fun output a b => do
    emit (.add a.ref b.ref output)
    pure ⟨Id.run (base.add output a.value b.value), output⟩
  sub := fun output a b => do
    emit (.sub a.ref b.ref output)
    pure ⟨Id.run (base.sub output a.value b.value), output⟩
  mul := fun output a b => do
    emit (.mul a.ref b.ref output)
    pure ⟨Id.run (base.mul output a.value b.value), output⟩
  square := fun output a => do
    emit (.square a.ref output)
    pure ⟨Id.run (base.square output a.value), output⟩
  inv := fun output a => do
    emit (.inv a.ref output)
    pure ⟨Id.run (base.inv output a.value), output⟩
  neg := fun output a => do
    emit (.neg a.ref output)
    pure ⟨Id.run (base.neg output a.value), output⟩

def mulDag : List Event :=
  [.mul .a0 .b0 .v0,
   .mul .a1 .b1 .v1,
   .add .a0 .a1 .aSum,
   .add .b0 .b1 .bSum,
   .mul .aSum .bSum .cross,
   .add .v0 .v1 .vSum,
   .sub .cross .vSum .c1,
   .sub .v0 .v1 .c0]

def invDag : List Event :=
  [.square .a0 .a0Square,
   .square .a1 .a1Square,
   .add .a0Square .a1Square .norm,
   .inv .norm .normInv,
   .mul .a0 .normInv .c0,
   .neg .a1 .negA1,
   .mul .negA1 .normInv .c1]

theorem runMulWith_audit_events {Wire Cell : Type}
    (base : Ops Wire Id Cell) (a0 a1 b0 b1 : Wire) :
    (Id.run ((runMulWith (auditOpsOf base) a0 a1 b0 b1).run [])).2 =
      mulDag := by
  unfold runMulWith auditOpsOf emit mulDag
  rfl

theorem runInvWith_audit_events {Wire Cell : Type}
    (base : Ops Wire Id Cell) (a0 a1 : Wire) :
    (Id.run ((runInvWith (auditOpsOf base) a0 a1).run [])).2 = invDag := by
  unfold runInvWith auditOpsOf emit invDag
  rfl

theorem runMulWith_audit_values {Wire Cell : Type} (base : Ops Wire Id Cell)
    (a0 a1 b0 b1 : Wire) :
    let audited := Id.run ((runMulWith (auditOpsOf base) a0 a1 b0 b1).run [])
    (audited.1.1.value, audited.1.2.value) =
      Id.run (runMulWith base a0 a1 b0 b1) := by
  unfold runMulWith auditOpsOf emit
  rfl

theorem runInvWith_audit_values {Wire Cell : Type} (base : Ops Wire Id Cell)
    (a0 a1 : Wire) :
    let audited := Id.run ((runInvWith (auditOpsOf base) a0 a1).run [])
    (audited.1.1.value, audited.1.2.value) =
      Id.run (runInvWith base a0 a1) := by
  unfold runInvWith auditOpsOf emit
  rfl

theorem runMulWith_audit_result {Wire Cell Result : Type}
    (base : Ops Wire Id Cell) (construct : Wire → Wire → Result)
    (a0 a1 b0 b1 : Wire) :
    let audited := Id.run ((runMulWith (auditOpsOf base) a0 a1 b0 b1).run [])
    let direct := Id.run (runMulWith base a0 a1 b0 b1)
    construct (base.value audited.1.1.value)
        (base.value audited.1.2.value) =
      construct (base.value direct.1) (base.value direct.2) := by
  have h := runMulWith_audit_values base a0 a1 b0 b1
  dsimp only at h ⊢
  exact congrArg (fun result : Cell × Cell =>
    construct (base.value result.1) (base.value result.2)) h

theorem runInvWith_audit_result {Wire Cell Result : Type}
    (base : Ops Wire Id Cell) (construct : Wire → Wire → Result)
    (a0 a1 : Wire) :
    let audited := Id.run ((runInvWith (auditOpsOf base) a0 a1).run [])
    let direct := Id.run (runInvWith base a0 a1)
    construct (base.value audited.1.1.value)
        (base.value audited.1.2.value) =
      construct (base.value direct.1) (base.value direct.2) := by
  have h := runInvWith_audit_values base a0 a1
  dsimp only at h ⊢
  exact congrArg (fun result : Cell × Cell =>
    construct (base.value result.1) (base.value result.2)) h

end Challenge.Bls12381.ProofSupport.Fp2.SourceProgram
