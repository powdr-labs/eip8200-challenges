import Challenge.Bls12381.ProofSupport.Fp2SourcePrimitives
import Challenge.Bls12381.ProofSupport.Fp2SourceProgram

set_option warningAsError true

/-! # Direct and auditable interpretations of the Fp2 source programs -/

namespace Challenge.Bls12381.ProofSupport.Fp2

abbrev SourceRef := SourceProgram.Ref
abbrev SourceEvent := SourceProgram.Event
abbrev SourceOps (M : Type → Type) [Monad M] (Cell : Type) :=
  SourceProgram.Ops Fp.Limbs M Cell
abbrev AuditCell := SourceProgram.AuditCell Fp.Limbs
abbrev AuditM := SourceProgram.AuditM

def runMulSourceWith {M : Type → Type} [Monad M] {Cell : Type}
    (ops : SourceOps M Cell) (a b : Repr) : M (Cell × Cell) :=
  SourceProgram.runMulWith ops a.c0 a.c1 b.c0 b.c1

def runInvSourceWith {M : Type → Type} [Monad M] {Cell : Type}
    (ops : SourceOps M Cell) (a : Repr) : M (Cell × Cell) :=
  SourceProgram.runInvWith ops a.c0 a.c1

def directSourceOps : SourceOps Id Fp.Limbs where
  input := fun _ a => a
  value := id
  add := fun _ a b => sourceAdd a b
  sub := fun _ a b => sourceSub a b
  mul := fun _ a b => sourceMul a b
  square := fun _ a => sourceSquare a
  inv := fun _ a => sourceInv a
  neg := fun _ a => sourceNeg a

theorem directSourceOps_input (ref : SourceRef) (a : Fp.Limbs) :
    directSourceOps.input ref a = a := rfl

theorem directSourceOps_value (a : Fp.Limbs) :
    directSourceOps.value a = a := rfl

theorem directSourceOps_add (output : SourceRef) (a b : Fp.Limbs) :
    Id.run (directSourceOps.add output a b) = sourceAdd a b := rfl

theorem directSourceOps_sub (output : SourceRef) (a b : Fp.Limbs) :
    Id.run (directSourceOps.sub output a b) = sourceSub a b := rfl

theorem directSourceOps_mul (output : SourceRef) (a b : Fp.Limbs) :
    Id.run (directSourceOps.mul output a b) = sourceMul a b := rfl

theorem directSourceOps_square (output : SourceRef) (a : Fp.Limbs) :
    Id.run (directSourceOps.square output a) = sourceSquare a := rfl

theorem directSourceOps_inv (output : SourceRef) (a : Fp.Limbs) :
    Id.run (directSourceOps.inv output a) = sourceInv a := rfl

theorem directSourceOps_neg (output : SourceRef) (a : Fp.Limbs) :
    Id.run (directSourceOps.neg output a) = sourceNeg a := rfl

theorem canonical_directSourceOps_add (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.add output a b)) := by
  rw [directSourceOps_add]
  exact canonical_sourceAdd ha hb

theorem canonical_directSourceOps_sub (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.sub output a b)) := by
  rw [directSourceOps_sub]
  exact canonical_sourceSub ha hb

theorem canonical_directSourceOps_mul (output : SourceRef) {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Id.run (directSourceOps.mul output a b)) := by
  rw [directSourceOps_mul]
  exact canonical_sourceMul ha hb

theorem canonical_directSourceOps_square (output : SourceRef) {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    Fp.Canonical (Id.run (directSourceOps.square output a)) := by
  rw [directSourceOps_square]
  exact canonical_sourceSquare ha

theorem canonical_directSourceOps_inv (output : SourceRef) {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    Fp.Canonical (Id.run (directSourceOps.inv output a)) := by
  rw [directSourceOps_inv]
  exact canonical_sourceInv ha

theorem canonical_directSourceOps_neg (output : SourceRef) {a : Fp.Limbs}
    (ha : Fp.Canonical a) :
    Fp.Canonical (Id.run (directSourceOps.neg output a)) := by
  rw [directSourceOps_neg]
  exact canonical_sourceNeg ha

/-- Runtime multiplication. The direct interpreter has `Cell = Fp.Limbs`
and carries no audit state. -/
def mulSource (a b : Repr) : Repr :=
  let result := Id.run (runMulSourceWith directSourceOps a b)
  mkRepr (directSourceOps.value result.1) (directSourceOps.value result.2)

/-- Runtime inversion through the same program and direct interpreter. -/
def invSource (a : Repr) : Repr :=
  let result := Id.run (runInvSourceWith directSourceOps a)
  mkRepr (directSourceOps.value result.1) (directSourceOps.value result.2)

def auditSourceOps : SourceOps AuditM AuditCell :=
  SourceProgram.auditOpsOf directSourceOps

structure AuditedSourceRun where
  result : Repr
  events : List SourceEvent

def mulSourceDag : List SourceEvent := SourceProgram.mulDag

/-- Audit interpretation of the same multiplication program. -/
def runMulSource (a b : Repr) : AuditedSourceRun :=
  let run := Id.run ((runMulSourceWith auditSourceOps a b).run [])
  { result := mkRepr (directSourceOps.value run.1.1.value)
      (directSourceOps.value run.1.2.value)
    events := run.2 }

theorem runMulSource_events (a b : Repr) :
    (runMulSource a b).events = mulSourceDag := by
  exact SourceProgram.runMulWith_audit_events directSourceOps
    a.c0 a.c1 b.c0 b.c1

def invSourceDag : List SourceEvent := SourceProgram.invDag

/-- Audit interpretation of the same inversion program. -/
def runInvSource (a : Repr) : AuditedSourceRun :=
  let run := Id.run ((runInvSourceWith auditSourceOps a).run [])
  { result := mkRepr (directSourceOps.value run.1.1.value)
      (directSourceOps.value run.1.2.value)
    events := run.2 }

theorem runInvSource_events (a : Repr) :
    (runInvSource a).events = invSourceDag := by
  exact SourceProgram.runInvWith_audit_events directSourceOps a.c0 a.c1

theorem runMulSource_value (a b : Repr) :
    (runMulSource a b).result = mulSource a b := by
  exact SourceProgram.runMulWith_audit_result directSourceOps mkRepr
    a.c0 a.c1 b.c0 b.c1

theorem runInvSource_value (a : Repr) :
    (runInvSource a).result = invSource a := by
  exact SourceProgram.runInvWith_audit_result directSourceOps mkRepr a.c0 a.c1

end Challenge.Bls12381.ProofSupport.Fp2
