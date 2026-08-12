import Challenge.Bls12381.Vectors
import Challenge.Bls12381G1Add.Scorer
import Challenge.Bls12381G1Msm.Scorer
import Challenge.Bls12381G2Add.Scorer
import Challenge.Bls12381G2Msm.Scorer
import Challenge.Bls12381MapFpToG1.Scorer
import Challenge.Bls12381MapFp2ToG2.Scorer
import Challenge.Bls12381Pairing.Scorer

set_option warningAsError true

namespace Checks.Bls12381Conformance

open Challenge.Bls12381

-- One non-trivial official output vector for every EIP-2537 operation.
#guard Challenge.Bls12381G1Add.spec Vectors.g1Add.input = some Vectors.g1Add.expected
#guard Challenge.Bls12381G1Msm.spec Vectors.g1Msm.input = some Vectors.g1Msm.expected
#guard Challenge.Bls12381G2Add.spec Vectors.g2Add.input = some Vectors.g2Add.expected
#guard Challenge.Bls12381G2Msm.spec Vectors.g2Msm.input = some Vectors.g2Msm.expected
#guard Challenge.Bls12381MapFpToG1.spec Vectors.mapFpToG1.input = some Vectors.mapFpToG1.expected
#guard Challenge.Bls12381MapFp2ToG2.spec Vectors.mapFp2ToG2.input = some Vectors.mapFp2ToG2.expected
#guard Challenge.Bls12381Pairing.spec Vectors.pairing.input = some Vectors.pairing.expected

#guard Gas.precompileCost .g1Add Vectors.g1Add.input = Vectors.g1Add.gas
#guard Gas.precompileCost .g1Msm Vectors.g1Msm.input = Vectors.g1Msm.gas
#guard Gas.precompileCost .g2Add Vectors.g2Add.input = Vectors.g2Add.gas
#guard Gas.precompileCost .g2Msm Vectors.g2Msm.input = Vectors.g2Msm.gas
#guard Gas.precompileCost .mapFpToG1 Vectors.mapFpToG1.input = Vectors.mapFpToG1.gas
#guard Gas.precompileCost .mapFp2ToG2 Vectors.mapFp2ToG2.input = Vectors.mapFp2ToG2.gas
#guard Gas.precompileCost .pairing Vectors.pairing.input = Vectors.pairing.gas

-- Addition accepts on-curve points outside the prime-order subgroup, while
-- MSM and pairing must reject them even when their scalar/partner is zero.
#guard Challenge.Bls12381G1Add.spec Vectors.g1AddNonSubgroup.input =
  some Vectors.g1AddNonSubgroup.expected
#guard Challenge.Bls12381G2Add.spec Vectors.g2AddNonSubgroup.input =
  some Vectors.g2AddNonSubgroup.expected
#guard Challenge.Bls12381G1Msm.spec Vectors.g1MsmNonSubgroup = none
#guard Challenge.Bls12381G2Msm.spec Vectors.g2MsmNonSubgroup = none
#guard Challenge.Bls12381Pairing.spec Vectors.pairingG1NonSubgroup = none
#guard Challenge.Bls12381Pairing.spec Vectors.pairingG2NonSubgroup = none

-- The candidate scorer exercises the same compact cases rather than only
-- zero/length smoke tests.
#guard Challenge.Bls12381G1Add.Scorer.vectors.any (fun v => v.input = Vectors.g1Add.input)
#guard Challenge.Bls12381G1Msm.Scorer.vectors.any (fun v => v.input = Vectors.g1Msm.input)
#guard Challenge.Bls12381G1Msm.Scorer.vectors.any (fun v => v.input = Vectors.g1MsmNonSubgroup)
#guard Challenge.Bls12381G2Add.Scorer.vectors.any (fun v => v.input = Vectors.g2Add.input)
#guard Challenge.Bls12381G2Msm.Scorer.vectors.any (fun v => v.input = Vectors.g2Msm.input)
#guard Challenge.Bls12381G2Msm.Scorer.vectors.any (fun v => v.input = Vectors.g2MsmNonSubgroup)
#guard Challenge.Bls12381MapFpToG1.Scorer.vectors.any (fun v => v.input = Vectors.mapFpToG1.input)
#guard Challenge.Bls12381MapFp2ToG2.Scorer.vectors.any (fun v => v.input = Vectors.mapFp2ToG2.input)
#guard Challenge.Bls12381Pairing.Scorer.vectors.any (fun v => v.input = Vectors.pairing.input)
#guard Challenge.Bls12381Pairing.Scorer.vectors.any (fun v => v.input = Vectors.pairingG1NonSubgroup)
#guard Challenge.Bls12381Pairing.Scorer.vectors.any (fun v => v.input = Vectors.pairingG2NonSubgroup)

-- Compact gas-table regression points, including floor-length transitions,
-- the repeated G2 entries at k = 98/99, and the k > 128 clamp.
#guard Gas.precompileCost .g1Msm (Vectors.zeros 159) = 0
#guard Gas.precompileCost .g1Msm (Vectors.zeros 160) = 12000
#guard Gas.precompileCost .g1Msm (Vectors.zeros 319) = 12000
#guard Gas.precompileCost .g1Msm (Vectors.zeros 320) = 22776
#guard Gas.precompileCost .g1Msm (Vectors.zeros (160 * 128)) = 797184
#guard Gas.precompileCost .g1Msm (Vectors.zeros (160 * 129)) = 803412

#guard Gas.precompileCost .g2Msm (Vectors.zeros 287) = 0
#guard Gas.precompileCost .g2Msm (Vectors.zeros 288) = 22500
#guard Gas.precompileCost .g2Msm (Vectors.zeros 576) = 45000
#guard Gas.precompileCost .g2Msm (Vectors.zeros (288 * 98)) = 1201725
#guard Gas.precompileCost .g2Msm (Vectors.zeros (288 * 99)) = 1213987
#guard Gas.precompileCost .g2Msm (Vectors.zeros (288 * 128)) = 1509120
#guard Gas.precompileCost .g2Msm (Vectors.zeros (288 * 129)) = 1520910

#guard Gas.precompileCost .pairing (Vectors.zeros 383) = 37700
#guard Gas.precompileCost .pairing (Vectors.zeros 384) = 70300

end Checks.Bls12381Conformance
