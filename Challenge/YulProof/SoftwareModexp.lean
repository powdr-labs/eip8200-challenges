import Challenge.YulProof.ClosedEvmDialect
import Challenge.YulProof.EvmState
import YulSemantics.BigStep

set_option warningAsError true

/-!
# Local software modular-exponentiation contracts

This module provides a semantic linking boundary for a Yul function which
implements modular exponentiation locally.  It deliberately says nothing
about a particular source AST, compiler, EVM artifact, or native precompile.

An implementation supplies an argument encoding, input invariant, result
relation, and writable memory regions.  `Correct` then states the function-call
contract in the closed EVM dialect.  The lookup premise makes the contract
usable from a larger host function environment without baking that host into
the component interface.
-/

namespace Challenge.YulProof.SoftwareModexp

open YulSemantics
open YulSemantics.EVM

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

/-- A half-open byte-address interval `[start, start + length)`. -/
structure MemoryRegion where
  start : Nat
  length : Nat
deriving DecidableEq, Repr

def MemoryRegion.Contains (region : MemoryRegion) (address : Nat) : Prop :=
  region.start ≤ address ∧ address < region.start + region.length

/-- Memory outside the component's declared writable regions is unchanged. -/
def MemoryFrame (regions : List MemoryRegion) (before after : EvmState) : Prop :=
  ∀ address, (∀ region ∈ regions, ¬ region.Contains address) →
    after.memory address = before.memory address

namespace MemoryFrame

theorem refl (regions : List MemoryRegion) (st : EvmState) :
    MemoryFrame regions st st := by
  intro _ _
  rfl

theorem trans {regions : List MemoryRegion} {first middle last : EvmState}
    (hfirst : MemoryFrame regions first middle)
    (hlast : MemoryFrame regions middle last) :
    MemoryFrame regions first last := by
  intro address houtside
  rw [hlast address houtside, hfirst address houtside]

/-- A component declaring no writable regions preserves memory exactly. -/
theorem empty_iff (before after : EvmState) :
    MemoryFrame [] before after ↔ after.memory = before.memory := by
  constructor
  · intro h
    funext address
    exact h address (by simp)
  · intro h _ _
    exact congrFun h _

end MemoryFrame

/-- Non-memory state is preserved by a normally returning local helper.

`activeWords` is intentionally absent: ordinary memory writes may increase the
EVM memory high-water mark.  Memory itself is governed by `MemoryFrame`. -/
structure StateFrame (before after : EvmState) : Prop where
  storage : after.storage = before.storage
  transient : after.transient = before.transient
  env : after.env = before.env
  returndata : after.returndata = before.returndata
  logs : after.logs = before.logs
  selfdestructs : after.selfdestructs = before.selfdestructs
  halted : after.halted = before.halted

namespace StateFrame

theorem refl (st : EvmState) : StateFrame st st := by
  constructor <;> rfl

theorem trans {first middle last : EvmState}
    (hfirst : StateFrame first middle) (hlast : StateFrame middle last) :
    StateFrame first last where
  storage := hlast.storage.trans hfirst.storage
  transient := hlast.transient.trans hfirst.transient
  env := hlast.env.trans hfirst.env
  returndata := hlast.returndata.trans hfirst.returndata
  logs := hlast.logs.trans hfirst.logs
  selfdestructs := hlast.selfdestructs.trans hfirst.selfdestructs
  halted := hlast.halted.trans hfirst.halted

end StateFrame

/-- Implementation-independent ABI and refinement predicates for one local
software modular-exponentiation function.

`Request` may describe a completely generic operation or a specialization
such as exponentiation in one fixed prime field.  `pre` owns the representation
of inputs in the argument words and memory.  `post` relates returned words and
the final state to the mathematical result. -/
structure Interface (Request : Type) where
  arguments : Request → List U256
  pre : EvmState → Request → Prop
  post : Request → List U256 → EvmState → Prop
  writes : Request → List MemoryRegion

/-- A local function implements `interface` in the closed EVM dialect.

The callee environment is explicit because Yul function lookup returns both a
declaration and its lexical environment.  A caller may use any larger function
environment whose lookup of `name` resolves to this component. -/
def Correct {Request : Type} (calleeFuns : FunEnv D) (name : Ident)
    (decl : FDecl D) (interface : Interface Request) : Prop :=
  ∀ {callerFuns : FunEnv D} {V : VEnv D} {st st1 : EvmState}
      {args : List (Expr Op)} (request : Request),
    lookupFun callerFuns name = some (decl, calleeFuns) →
    EvalArgs D callerFuns V st args (.vals (interface.arguments request) st1) →
    interface.pre st1 request →
    ∃ values final,
      EvalExpr D callerFuns V st (.call name args) (.vals values final) ∧
      interface.post request values final ∧
      StateFrame st1 final ∧
      MemoryFrame (interface.writes request) st1 final

namespace Correct

/-- Apply a component contract at one resolved source call. -/
theorem call {Request : Type} {calleeFuns : FunEnv D} {name : Ident}
    {decl : FDecl D}
    {interface : Interface Request}
    (hcorrect : Correct calleeFuns name decl interface)
    {callerFuns : FunEnv D} {V : VEnv D} {st st1 : EvmState}
    {args : List (Expr Op)} {request : Request}
    (hlookup : lookupFun callerFuns name = some (decl, calleeFuns))
    (hargs : EvalArgs D callerFuns V st args
      (.vals (interface.arguments request) st1))
    (hpre : interface.pre st1 request) :
    ∃ values final,
      EvalExpr D callerFuns V st (.call name args) (.vals values final) ∧
      interface.post request values final ∧
      StateFrame st1 final ∧
      MemoryFrame (interface.writes request) st1 final :=
  hcorrect request hlookup hargs hpre

end Correct

end Challenge.YulProof.SoftwareModexp
