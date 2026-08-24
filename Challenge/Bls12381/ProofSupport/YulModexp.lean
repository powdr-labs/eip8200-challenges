import Challenge.Bls12381.ProofSupport.FpInv
import Challenge.YulProof.SoftwareModexp
import Challenge.YulProof.SoftwareModexpMath

set_option warningAsError true

/-!
# BLS12-381 adapter for a local software MODEXP component

This module specializes the implementation-independent local-function contract
to the existing two-limb BLS base-field model.  It remains independent of any
concrete Yul declaration, arithmetic algorithm, or function environment.  Its
postcondition states canonical modular exponentiation directly.  A separate
adapter lets implementations reuse the existing Montgomery development when
that is how their source result was obtained.
-/

namespace Challenge.Bls12381.ProofSupport.YulModexp

open YulSemantics
open YulSemantics.EVM

private abbrev D := Challenge.YulProof.ClosedEvm.dialect

/-- Mathematical request carried by the BLS software-MODEXP function.  The
argument ABI and any exponent-memory representation remain implementation
parameters of `interface`. -/
structure Request where
  baseHi : U256
  baseLo : U256
  exponent : List UInt8
deriving DecidableEq, Repr

def Request.base (request : Request) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv request.baseHi
    lo := YulEvmCompiler.conv request.baseLo }

/-- The implementation-free natural-number MODEXP operation represented by a
BLS request.  BLS fixes the modulus and its canonical byte width, while the
source ABI remains a separate concern. -/
def Request.operation (request : Request) :
    Challenge.YulProof.SoftwareModexpMath.Operation :=
  { base := Fp.value request.base
    exponent := Fp.bytesValue request.exponent
    modulus := EvmSemantics.Crypto.Bls12381.p
    outputSize := 48 }

/-- Mathematical modular-exponentiation result for one canonical BLS field
base.  This predicate does not select an implementation or representation
algorithm. -/
def LimbsRefines (request : Request) (output : Fp.Limbs) : Prop :=
  Fp.Canonical output ∧
    (Fp.value output : Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) =
      (Fp.value request.base :
        Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) ^
          Fp.bytesValue request.exponent

/-- The field-facing result relation implies the same implementation-free
natural-number MODEXP result used by the general EIP-198 Yul implementation. -/
theorem LimbsRefines.resultNat {request : Request} {output : Fp.Limbs}
    (hrefines : LimbsRefines request output) :
    Challenge.YulProof.SoftwareModexpMath.ResultNat request.operation
      (Fp.value output) := by
  unfold Challenge.YulProof.SoftwareModexpMath.ResultNat
    Challenge.YulProof.SoftwareModexpMath.Operation.resultNat
    Request.operation
  apply Nat.ModEq.eq_of_lt_of_lt
  · rw [← ZMod.natCast_eq_natCast_iff]
    exact hrefines.2.trans
      (Challenge.Bls12381.ProofSupport.PrimeField.natCast_modPow_eq_pow
        (Fp.value request.base) (Fp.bytesValue request.exponent)
        EvmSemantics.Crypto.Bls12381.p
        (by norm_num [EvmSemantics.Crypto.Bls12381.p,
          EvmSemantics.Crypto.Bls12381.absU])).symm
  · exact hrefines.1.2
  · exact Challenge.EvmProof.ModPow.eval_lt
      (by norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU])

/-- Exact returned-word refinement expected from any two-limb BLS MODEXP
component. -/
def Refines (request : Request) (values : List U256) : Prop :=
  ∃ resultHi resultLo,
    values = [resultHi, resultLo] ∧
      LimbsRefines request
        ({ hi := YulEvmCompiler.conv resultHi
           lo := YulEvmCompiler.conv resultLo } : Fp.Limbs)

/-- The existing source-faithful Montgomery implementation discharges the
implementation-independent mathematical result predicate. -/
theorem montgomeryPowDecoded_refines (request : Request)
    (hcanonical : Fp.Canonical request.base) :
    LimbsRefines request
      (Fp.montgomeryPowDecoded request.base request.exponent) :=
  ⟨Fp.canonical_montgomeryPowDecoded hcanonical request.exponent,
    Fp.lawful_montgomeryPowDecoded hcanonical request.exponent⟩

/-- Word-level adapter used after proving that a concrete Yul result follows
the existing Montgomery schedule. -/
theorem Refines.of_montgomeryPowDecoded
    (request : Request) (resultHi resultLo : U256)
    (hcanonical : Fp.Canonical request.base)
    (hresult :
      ({ hi := YulEvmCompiler.conv resultHi
         lo := YulEvmCompiler.conv resultLo } : Fp.Limbs) =
        Fp.montgomeryPowDecoded request.base request.exponent) :
    Refines request [resultHi, resultLo] := by
  refine ⟨resultHi, resultLo, rfl, ?_⟩
  rw [hresult]
  exact montgomeryPowDecoded_refines request hcanonical

/-- BLS specialization of the generic software-MODEXP interface.

The source adapter chooses its own call arguments, memory input invariant, and
writable regions.  Canonicality of the base is the only arithmetic precondition
owned by this layer. -/
def interface
    (arguments : Request → List U256)
    (inputRep : EvmState → Request → Prop)
    (writes : Request → List Challenge.YulProof.SoftwareModexp.MemoryRegion) :
    Challenge.YulProof.SoftwareModexp.Interface Request where
  arguments := arguments
  pre := fun st request => Fp.Canonical request.base ∧ inputRep st request
  post := fun request values _ => Refines request values
  writes := writes

/-- A closed-dialect local Yul function implements BLS base-field modular
exponentiation for the chosen source ABI. -/
def Correct (calleeFuns : FunEnv D) (name : Ident) (decl : FDecl D)
    (arguments : Request → List U256)
    (inputRep : EvmState → Request → Prop)
    (writes : Request → List Challenge.YulProof.SoftwareModexp.MemoryRegion) :
    Prop :=
  Challenge.YulProof.SoftwareModexp.Correct calleeFuns name decl
    (interface arguments inputRep writes)

/-! ## Fixed BLS inversion ABI -/

/-- Request made by the G1ADD field-inversion helper. -/
def inversionRequest (baseHi baseLo : U256) : Request :=
  { baseHi := baseHi, baseLo := baseLo, exponent := Fp.pMinus2Bytes }

/-- The proof-friendly source inversion helper receives only the two base
words; its exponent and modulus are fixed source constants. -/
def inversionArguments (request : Request) : List U256 :=
  [request.baseHi, request.baseLo]

/-- Restrict the fixed-constant helper to its actual `p - 2` operation. -/
def inversionInput (_ : EvmState) (request : Request) : Prop :=
  request.exponent = Fp.pMinus2Bytes

/-- Fixed-inversion interface with implementation-declared scratch regions.

The current proof-friendly helper may keep its Montgomery temporaries on the
Yul stack, while another implementation may use the four-word scratch layout
from `Fp.sol`.  Both instantiate the same arithmetic contract and explicitly
state their memory frame. -/
def inversionInterface
    (writes : Request → List Challenge.YulProof.SoftwareModexp.MemoryRegion) :
    Challenge.YulProof.SoftwareModexp.Interface Request :=
  interface inversionArguments inversionInput writes

/-- Closed-dialect contract consumed by G1ADD for its fixed-exponent local
software inversion function. -/
def InversionCorrect (calleeFuns : FunEnv D) (name : Ident) (decl : FDecl D)
    (writes : Request → List Challenge.YulProof.SoftwareModexp.MemoryRegion) : Prop :=
  Challenge.YulProof.SoftwareModexp.Correct calleeFuns name decl
    (inversionInterface writes)

/-- The BLS result relation always exposes exactly two source words. -/
theorem Refines.values_length {request : Request} {values : List U256}
    (hrefines : Refines request values) : values.length = 2 := by
  obtain ⟨resultHi, resultLo, rfl, _⟩ := hrefines
  rfl

/-- Specializing a correct MODEXP result to the fixed exponent `p - 2`
produces the already-certified source-faithful inversion result. -/
theorem Refines.pMinus2_eq_invCanonical
    {baseHi baseLo : U256} {values : List U256}
    (hrefines : Refines
      { baseHi := baseHi, baseLo := baseLo, exponent := Fp.pMinus2Bytes }
      values)
    (hcanonical : Fp.Canonical
      ({ hi := YulEvmCompiler.conv baseHi
         lo := YulEvmCompiler.conv baseLo } : Fp.Limbs)) :
    ∃ resultHi resultLo,
      values = [resultHi, resultLo] ∧
        ({ hi := YulEvmCompiler.conv resultHi
           lo := YulEvmCompiler.conv resultLo } : Fp.Limbs) =
          Fp.invCanonical
            ({ hi := YulEvmCompiler.conv baseHi
               lo := YulEvmCompiler.conv baseLo } : Fp.Limbs) := by
  obtain ⟨resultHi, resultLo, hvalues, hresult⟩ := hrefines
  refine ⟨resultHi, resultLo, hvalues, ?_⟩
  apply Fp.limbs_ext_of_value_eq
  apply Fp.value_eq_of_lawful_eq hresult.1
    (Fp.canonical_invCanonical hcanonical)
  rw [Fp.lawful_invCanonical hcanonical, hresult.2,
    Fp.bytesValue_pMinus2Bytes, Fp.lawful_pow_pMinus2_eq_inv]
  rfl

/-- Consumer-facing inversion theorem for a returned software-MODEXP pair. -/
theorem Refines.pMinus2_toLawful
    {baseHi baseLo : U256} {values : List U256}
    (hrefines : Refines
      { baseHi := baseHi, baseLo := baseLo, exponent := Fp.pMinus2Bytes }
      values) :
    ∃ resultHi resultLo,
      values = [resultHi, resultLo] ∧
      (Fp.value
          ({ hi := YulEvmCompiler.conv resultHi
             lo := YulEvmCompiler.conv resultLo } : Fp.Limbs) :
            Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) =
          (Fp.value
            ({ hi := YulEvmCompiler.conv baseHi
               lo := YulEvmCompiler.conv baseLo } : Fp.Limbs) :
            Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp)⁻¹ := by
  obtain ⟨resultHi, resultLo, hvalues, hresult⟩ := hrefines
  refine ⟨resultHi, resultLo, hvalues, ?_⟩
  rw [hresult.2, Fp.bytesValue_pMinus2Bytes,
    Fp.lawful_pow_pMinus2_eq_inv]
  rfl

/-- Canonicality is part of the implementation-independent result contract. -/
theorem Refines.canonical
    {request : Request} {values : List U256}
    (hrefines : Refines request values) :
    ∃ resultHi resultLo,
      values = [resultHi, resultLo] ∧
        Fp.Canonical
          ({ hi := YulEvmCompiler.conv resultHi
             lo := YulEvmCompiler.conv resultLo } : Fp.Limbs) := by
  obtain ⟨resultHi, resultLo, hvalues, hresult⟩ := hrefines
  exact ⟨resultHi, resultLo, hvalues, hresult.1⟩

end Challenge.Bls12381.ProofSupport.YulModexp
