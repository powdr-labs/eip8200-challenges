import Mathlib.Data.Nat.Init

set_option warningAsError true

/-!
# Parametric binary scalar-multiplication program

This module contains no curve arithmetic.  One monadic program is interpreted
directly for runtime use and with a state writer for control-flow audits.  An
audit therefore records operations when they are invoked, independently of
whether their returned values are subsequently used.
-/

namespace Challenge.Bls12381.ProofSupport.ScalarMul.Program

/-- Curve operations observable in the binary scalar schedule. -/
inductive Event where
  | add
  | double
deriving BEq, DecidableEq

/-- Operations required by the one authoritative binary scalar program. -/
structure Ops (Point : Type) (M : Type → Type) [Monad M] where
  zero : Point
  add : Point → Point → M Point
  double : Point → M Point

/-- Right-to-left binary double-and-add with an explicit scalar-one terminal
branch.  In particular, `double` is not invoked for scalars zero or one. -/
def runWith {Point : Type} {M : Type → Type} [Monad M]
    (ops : Ops Point M) (scalar : Nat) (point : Point) : M Point :=
  if hzero : scalar = 0 then
    pure ops.zero
  else if scalar = 1 then
    pure point
  else do
    let doubled ← ops.double point
    let rest ← runWith ops (scalar / 2) doubled
    if scalar % 2 = 1 then ops.add rest point else pure rest
termination_by scalar
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero hzero) Nat.one_lt_two

/-- Pure interpreter used by the executable scalar multiplication. -/
def directOps {Point : Type} (zero : Point) (add : Point → Point → Point)
    (double : Point → Point) : Ops Point Id where
  zero := zero
  add := fun left right => pure (add left right)
  double := fun point => pure (double point)

@[simp] theorem runWith_direct_zero {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    Id.run (runWith (directOps zero add double) 0 point) = zero := by
  rw [runWith]
  rfl

@[simp] theorem runWith_direct_one {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    Id.run (runWith (directOps zero add double) 1 point) = point := by
  rw [runWith]
  rfl

theorem runWith_direct_step {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) (hscalar : scalar ≠ 0) :
    Id.run (runWith (directOps zero add double) scalar point) =
      if scalar = 1 then point
      else if scalar % 2 = 1 then
          add (Id.run (runWith (directOps zero add double) (scalar / 2)
            (double point))) point
        else Id.run (runWith (directOps zero add double) (scalar / 2)
          (double point)) := by
  rw [runWith]
  simp only [hscalar, ↓reduceDIte]
  by_cases hone : scalar = 1
  · simp [hone]
  · simp only [hone, ↓reduceIte, directOps]
    by_cases hodd : scalar % 2 = 1
    · simp [hodd, Id.run, bind, pure]
    · simp [hodd, Id.run, bind, pure]

abbrev AuditM := StateM (List Event)

private def emit (event : Event) : AuditM Unit := fun events =>
  ((), events ++ [event])

/-- State-writer interpreter for the same program.  Every operation invocation
is logged before its result is returned. -/
def auditOps {Point : Type} (zero : Point) (add : Point → Point → Point)
    (double : Point → Point) : Ops Point AuditM where
  zero := zero
  add := fun left right => do
    emit .add
    pure (add left right)
  double := fun point => do
    emit .double
    pure (double point)

/-- Result and complete operation trace of the audit interpreter. -/
structure Audited (Point : Type) where
  value : Point
  events : List Event

/-- Run the authoritative program with the state-writer interpreter. -/
def audit {Point : Type} (zero : Point) (add : Point → Point → Point)
    (double : Point → Point) (scalar : Nat) (point : Point) : Audited Point :=
  let result := Id.run ((runWith (auditOps zero add double) scalar point).run [])
  { value := result.1, events := result.2 }

@[simp] theorem audit_zero_events {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    (audit zero add double 0 point).events = [] := by
  simp [audit, runWith, auditOps]

@[simp] theorem audit_one_events {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    (audit zero add double 1 point).events = [] := by
  simp [audit, runWith, auditOps]

@[simp] theorem audit_two_events {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    (audit zero add double 2 point).events = [.double] := by
  simp [audit, runWith, auditOps, StateT.run, Id.run]
  change ([] ++ [Event.double]) = [Event.double]
  rfl

@[simp] theorem audit_three_events {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    (audit zero add double 3 point).events = [.double, .add] := by
  simp [audit, runWith, auditOps, StateT.run, Id.run]
  change (([] ++ [Event.double]) ++ [Event.add]) =
    [Event.double, Event.add]
  rfl

/-- Auditing does not change the value computed by the direct interpreter. -/
theorem runWith_audit_value {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) (events : List Event) :
    (Id.run ((runWith (auditOps zero add double) scalar point).run events)).1 =
      Id.run (runWith (directOps zero add double) scalar point) := by
  induction scalar using Nat.strong_induction_on generalizing point events with
  | h scalar ih =>
      by_cases hzero : scalar = 0
      · subst scalar
        simp [runWith, auditOps, directOps]
      · by_cases hone : scalar = 1
        · subst scalar
          simp [runWith, auditOps, directOps]
        rw [runWith, runWith]
        simp only [hzero, hone, ↓reduceDIte, ↓reduceIte]
        by_cases hodd : scalar % 2 = 1
        · simp only [hodd, if_pos]
          change add
              (Id.run ((runWith (auditOps zero add double) (scalar / 2)
                (double point)).run (events ++ [.double]))).1 point =
            add (Id.run (runWith (directOps zero add double) (scalar / 2)
              (double point))) point
          rw [ih (scalar / 2)
            (Nat.div_lt_self (Nat.zero_lt_of_ne_zero hzero) Nat.one_lt_two)]
        · simp only [hodd]
          change
              (Id.run ((runWith (auditOps zero add double) (scalar / 2)
                (double point)).run (events ++ [.double]))).1 =
            Id.run (runWith (directOps zero add double) (scalar / 2)
              (double point))
          rw [ih (scalar / 2)
            (Nat.div_lt_self (Nat.zero_lt_of_ne_zero hzero) Nat.one_lt_two)]

/-- Public value bridge between the audit run and executable direct run. -/
theorem audit_value {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) :
    (audit zero add double scalar point).value =
      Id.run (runWith (directOps zero add double) scalar point) := by
  exact runWith_audit_value zero add double scalar point []

end Challenge.Bls12381.ProofSupport.ScalarMul.Program
