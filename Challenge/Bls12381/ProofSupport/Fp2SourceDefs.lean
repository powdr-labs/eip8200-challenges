import Challenge.Bls12381.ProofSupport.Fp2Representation
import Challenge.Bls12381.ProofSupport.FpAddSub
import Challenge.Bls12381.ProofSupport.FpMul
import Challenge.Bls12381.ProofSupport.FpSquare
import Challenge.Bls12381.ProofSupport.FpInv

set_option warningAsError true

/-! # Executable source-faithful BLS12-381 Fp2 schedules -/

namespace Challenge.Bls12381.ProofSupport.Fp2

/-- Exact componentwise `Fp2.add` call graph. -/
def addSource (a b : Repr) : Repr :=
  mkRepr (Fp.addSource a.c0 b.c0) (Fp.addSource a.c1 b.c1)

/-- Exact componentwise `Fp2.sub` call graph. -/
def subSource (a b : Repr) : Repr :=
  mkRepr (Fp.subSource a.c0 b.c0) (Fp.subSource a.c1 b.c1)

/-- Exact componentwise `Fp2.neg` call graph. -/
def negSource (a : Repr) : Repr :=
  mkRepr (Fp.negSource a.c0) (Fp.negSource a.c1)

/-- Exact three-multiplication Karatsuba schedule from `Fp2.mul`. -/
def mulV0Source (a b : Repr) : Fp.Limbs :=
  Fp.mulCanonical a.c0 b.c0

def mulV1Source (a b : Repr) : Fp.Limbs :=
  Fp.mulCanonical a.c1 b.c1

def mulRealSource (v0 v1 : Fp.Limbs) : Fp.Limbs :=
  Fp.subSource v0 v1

def mulImaginarySource (a b : Repr) (v0 v1 : Fp.Limbs) : Fp.Limbs :=
  Fp.subSource
    (Fp.mulCanonical
      (Fp.addSource a.c0 a.c1) (Fp.addSource b.c0 b.c1))
    (Fp.addSource v0 v1)

/-- Exact two-multiplication optimized schedule from `Fp2.sqr`. -/
def sqrRealSource (a : Repr) : Fp.Limbs :=
  Fp.mulCanonical
    (Fp.addSource a.c0 a.c1) (Fp.subSource a.c0 a.c1)

def sqrImaginarySource (product : Fp.Limbs) : Fp.Limbs :=
  Fp.addSource product product

def sqrProductSource (a : Repr) : Fp.Limbs :=
  Fp.mulCanonical a.c0 a.c1

def sqrC1Source (a : Repr) : Fp.Limbs :=
  sqrImaginarySource (sqrProductSource a)

def sqrSource (a : Repr) : Repr :=
  mkRepr (sqrRealSource a) (sqrC1Source a)

/-- Exact norm/invert/adjugate schedule from `Fp2.inv`. -/
def invNormSource (a : Repr) : Fp.Limbs :=
  Fp.addSource (Fp.squareCanonical a.c0) (Fp.squareCanonical a.c1)

def invRealSource (a0 normInv : Fp.Limbs) : Fp.Limbs :=
  Fp.mulCanonical a0 normInv

def invImaginarySource (a1 normInv : Fp.Limbs) : Fp.Limbs :=
  Fp.mulCanonical (Fp.negSource a1) normInv

/-- Exact componentwise scalar multiplication from `Fp2.mulFp`. -/
def mulFpSource (a : Repr) (s : Fp.Limbs) : Repr :=
  mkRepr (Fp.mulCanonical a.c0 s) (Fp.mulCanonical a.c1 s)

theorem sqrSource_eq (a : Repr) :
    sqrSource a = mkRepr (sqrRealSource a) (sqrC1Source a) := rfl

end Challenge.Bls12381.ProofSupport.Fp2
