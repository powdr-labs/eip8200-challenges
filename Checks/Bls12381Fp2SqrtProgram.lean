import Challenge.Bls12381.ProofSupport.Fp2SqrtProgram

set_option warningAsError true

namespace Checks.Bls12381Fp2SqrtProgram

open Challenge.Bls12381.ProofSupport.Fp2

example {Cell Pair : Type} (ops : SqrtProgram.Ops Cell Pair) (a : Pair) :
    SqrtProgram.run ops a =
      if ops.isZeroPair a then { exists_ := true, root := ops.zero }
      else
        let norm := ops.add (ops.square (ops.c0 a)) (ops.square (ops.c1 a))
        let t := ops.sqrt norm
        if !(ops.eqCell (ops.square t) norm) then
          { exists_ := false, root := ops.zero }
        else
          let alpha := ops.mul (ops.add (ops.c0 a) t) ops.invTwo
          let alphaRoot := ops.sqrt alpha
          let x0 :=
            if !(ops.eqCell (ops.square alphaRoot) alpha) then
              let beta := ops.mul (ops.sub (ops.c0 a) t) ops.invTwo
              ops.sqrt beta
            else alphaRoot
          let x1 :=
            if ops.isZeroCell x0 then
              ops.sqrt (ops.neg (ops.c0 a))
            else
              ops.mul (ops.c1 a) (ops.inv (ops.add x0 x0))
          let root := ops.pair x0 x1
          if !(ops.eqPair (ops.squarePair root) a) then
            { exists_ := false, root := ops.zero }
          else { exists_ := true, root } := rfl

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.SqrtProgram.run_good' does not depend on any axioms -/
#guard_msgs in
#print axioms SqrtProgram.run_good

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.SqrtProgram.run_refines' does not depend on any axioms -/
#guard_msgs in
#print axioms SqrtProgram.run_refines

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.SqrtProgram.run_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SqrtProgram.run_success

end Checks.Bls12381Fp2SqrtProgram
