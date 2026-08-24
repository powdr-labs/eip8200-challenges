// SPDX-License-Identifier: Apache-2.0
// Proof-friendly naive EIP-2537 G1ADD.
//
// Field elements are carried as (high128, low256) words. Multiplication uses
// an exact three-word schoolbook product and fixed-modulus Barrett reduction.
// Inversion is Fermat exponentiation in a two-word Montgomery domain. Every
// operation is ordinary local EVM arithmetic: no precompile or external call.
// The word schedules are adapted from evmification's MIT-licensed
// src/bls12381/Fp.sol and stay aligned with the shared Lean arithmetic model.
{
    function fpGeModulus(hi, lo) -> yes {
        let pHi := 0x1a0111ea397fe69a4b1ba7b6434bacd7
        let pLo := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
        yes := or(gt(hi, pHi), and(eq(hi, pHi), iszero(lt(lo, pLo))))
    }

    function fpValid(hi, lo) -> yes {
        yes := iszero(fpGeModulus(hi, lo))
    }

    function fpZero(hi, lo) -> yes {
        yes := and(iszero(hi), iszero(lo))
    }

    function fpEq(aHi, aLo, bHi, bLo) -> yes {
        yes := and(eq(aHi, bHi), eq(aLo, bLo))
    }

    function fpAdd(aHi, aLo, bHi, bLo) -> zHi, zLo {
        zLo := add(aLo, bLo)
        zHi := add(add(aHi, bHi), lt(zLo, aLo))
        if fpGeModulus(zHi, zLo) {
            let pHi := 0x1a0111ea397fe69a4b1ba7b6434bacd7
            let pLo := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
            let nextLo := sub(zLo, pLo)
            zHi := sub(zHi, add(pHi, gt(pLo, zLo)))
            zLo := nextLo
        }
    }

    function fpSub(aHi, aLo, bHi, bLo) -> zHi, zLo {
        zLo := sub(aLo, bLo)
        zHi := sub(sub(aHi, bHi), gt(bLo, aLo))
        let pHi := 0x1a0111ea397fe69a4b1ba7b6434bacd7
        if gt(zHi, pHi) {
            let pLo := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
            let nextLo := add(zLo, pLo)
            zHi := add(add(zHi, pHi), lt(nextLo, zLo))
            zLo := nextLo
        }
    }

    function fullMul(aHi, aLo, bHi, bLo) -> r2, r1, r0 {
        r0 := mul(aLo, bLo)
        let mm0 := mulmod(aLo, bLo, not(0))
        let hi0 := sub(sub(mm0, r0), lt(mm0, r0))

        let lo1 := mul(aHi, bLo)
        let mm1 := mulmod(aHi, bLo, not(0))
        let hi1 := sub(sub(mm1, lo1), lt(mm1, lo1))

        let lo2 := mul(aLo, bHi)
        let mm2 := mulmod(aLo, bHi, not(0))
        let hi2 := sub(sub(mm2, lo2), lt(mm2, lo2))

        r1 := add(hi0, lo1)
        let carry := lt(r1, hi0)
        let nextR1 := add(r1, lo2)
        carry := add(carry, lt(nextR1, r1))
        r1 := nextR1
        r2 := add(add(hi1, hi2), add(mul(aHi, bHi), carry))
    }

    function storeFp(ptr, hi, lo) {
        mstore(ptr, shl(128, hi))
        mstore(add(ptr, 16), lo)
    }

    function storeModulus(ptr) {
        storeFp(
            ptr,
            0x1a0111ea397fe69a4b1ba7b6434bacd7,
            0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
        )
    }

    function fpMul(aHi, aLo, bHi, bLo) -> zHi, zLo {
        let r2, r1, r0 := fullMul(aHi, aLo, bHi, bLo)
        zHi, zLo := fpReduceProduct(r2, r1, r0)
    }

    function fpInv(aHi, aLo) -> zHi, zLo {
        zHi, zLo := fpPowPMinus2(aHi, aLo)
    }

    function onCurve(xHi, xLo, yHi, yLo) -> yes {
        let lhsHi, lhsLo := fpMul(yHi, yLo, yHi, yLo)
        let x2Hi, x2Lo := fpMul(xHi, xLo, xHi, xLo)
        let rhsHi, rhsLo := fpMul(x2Hi, x2Lo, xHi, xLo)
        rhsHi, rhsLo := fpAdd(rhsHi, rhsLo, 0, 4)
        yes := fpEq(lhsHi, lhsLo, rhsHi, rhsLo)
    }

    function storePoint(xHi, xLo, yHi, yLo) {
        mstore(0, xHi)
        mstore(32, xLo)
        mstore(64, yHi)
        mstore(96, yLo)
    }

    if iszero(eq(calldatasize(), 256)) { invalid() }

    // Stage the two points in fixed memory words. This keeps only the active
    // arithmetic intermediates on the EVM stack; the verified backend targets
    // the pre-EIP-8024 DUP/SWAP16 instruction set.
    mstore(0, calldataload(0))
    mstore(32, calldataload(32))
    mstore(64, calldataload(64))
    mstore(96, calldataload(96))
    mstore(128, calldataload(128))
    mstore(160, calldataload(160))
    mstore(192, calldataload(192))
    mstore(224, calldataload(224))

    // The high words carry exactly the 16 EIP padding bytes followed by the
    // 128-bit high field limb.
    if or(or(shr(128, mload(0)), shr(128, mload(64))),
          or(shr(128, mload(128)), shr(128, mload(192)))) { invalid() }
    if iszero(and(and(fpValid(mload(0), mload(32)), fpValid(mload(64), mload(96))),
                  and(fpValid(mload(128), mload(160)), fpValid(mload(192), mload(224))))) {
        invalid()
    }

    // Keep the infinity flags inside a lexical scope so they are no longer
    // live when the finite-point arithmetic begins.
    {
        let inf1 := and(fpZero(mload(0), mload(32)), fpZero(mload(64), mload(96)))
        let inf2 := and(fpZero(mload(128), mload(160)), fpZero(mload(192), mload(224)))
        if and(iszero(inf1),
            iszero(onCurve(mload(0), mload(32), mload(64), mload(96)))) { invalid() }
        if and(iszero(inf2),
            iszero(onCurve(mload(128), mload(160), mload(192), mload(224)))) { invalid() }

        if and(inf1, inf2) { return(0, 128) }
        if inf1 {
            storePoint(mload(128), mload(160), mload(192), mload(224))
            return(0, 128)
        }
        if inf2 {
            return(0, 128)
        }
    }

    let lamHi, lamLo
    if fpEq(mload(0), mload(32), mload(128), mload(160)) {
        if iszero(fpEq(mload(64), mload(96), mload(192), mload(224))) {
            storePoint(0, 0, 0, 0)
            return(0, 128)
        }
        if fpZero(mload(64), mload(96)) {
            storePoint(0, 0, 0, 0)
            return(0, 128)
        }
        let xSqHi, xSqLo := fpMul(mload(0), mload(32), mload(0), mload(32))
        let numHi, numLo := fpAdd(xSqHi, xSqLo, xSqHi, xSqLo)
        numHi, numLo := fpAdd(numHi, numLo, xSqHi, xSqLo)
        let denHi, denLo := fpAdd(mload(64), mload(96), mload(64), mload(96))
        let denInvHi, denInvLo := fpInv(denHi, denLo)
        lamHi, lamLo := fpMul(numHi, numLo, denInvHi, denInvLo)
    }
    if iszero(fpEq(mload(0), mload(32), mload(128), mload(160))) {
        let numHi, numLo := fpSub(mload(192), mload(224), mload(64), mload(96))
        let denHi, denLo := fpSub(mload(128), mload(160), mload(0), mload(32))
        let denInvHi, denInvLo := fpInv(denHi, denLo)
        lamHi, lamLo := fpMul(numHi, numLo, denInvHi, denInvLo)
    }

    let x3Hi, x3Lo := fpMul(lamHi, lamLo, lamHi, lamLo)
    x3Hi, x3Lo := fpSub(x3Hi, x3Lo, mload(0), mload(32))
    x3Hi, x3Lo := fpSub(x3Hi, x3Lo, mload(128), mload(160))
    let deltaHi, deltaLo := fpSub(mload(0), mload(32), x3Hi, x3Lo)
    let y3Hi, y3Lo := fpMul(lamHi, lamLo, deltaHi, deltaLo)
    y3Hi, y3Lo := fpSub(y3Hi, y3Lo, mload(64), mload(96))
    storePoint(x3Hi, x3Lo, y3Hi, y3Lo)
    return(0, 128)

    function fpPowPMinus2(aHi, aLo) -> zHi, zLo {
        // Encode once, process the 380 remaining bits of the fixed nonzero
        // exponent p-2, then decode once. The leading one initializes acc.
        let baseLo, baseHi := montMul2(
            aLo, aHi,
            0xcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58,
            0x0010a8c1a49a064ff0a85a3f35446d0b
        )
        let accLo := baseLo
        let accHi := baseHi

        // The high limb of p-2 is 125 bits; bit 124 is the consumed leading 1.
        for { let bit := 124 } gt(bit, 0) {} {
            bit := sub(bit, 1)
            accLo, accHi := montMul2(accLo, accHi, accLo, accHi)
            if and(shr(bit, 0x1a0111ea397fe69a4b1ba7b6434bacd7), 1) {
                accLo, accHi := montMul2(accLo, accHi, baseLo, baseHi)
            }
        }

        for { let bit := 256 } gt(bit, 0) {} {
            bit := sub(bit, 1)
            accLo, accHi := montMul2(accLo, accHi, accLo, accHi)
            if and(shr(bit,
                0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaa9), 1) {
                accLo, accHi := montMul2(accLo, accHi, baseLo, baseHi)
            }
        }

        zLo, zHi := montMul2(accLo, accHi, 1, 0)
    }

    function fpReduceProduct(r2, r1, r0) -> zHi, zLo {
        // mu = floor(2^1024 / p). The six full products below compute
        // q = ((r2:r1) * mu) >> 768.
        let qLo
        let qHi
        {
            let m0 := 0xad397b918f6ff20d533b6c08511c60e2757079ace6bd401859778ceb4dabc4f8
            let m1 := 0x1b82741ff6a0a94bdf4771e0286779d3997167a058f1c07b13e207f56591ba2e
            let m2 := 0x9d835d2f3cc9e45ce28101b0cc7a6ba29

            let lo00 := mul(r1, m0)
            let mm := mulmod(r1, m0, not(0))
            let hi00 := sub(sub(mm, lo00), lt(mm, lo00))

            let lo01 := mul(r1, m1)
            mm := mulmod(r1, m1, not(0))
            let hi01 := sub(sub(mm, lo01), lt(mm, lo01))

            let lo02 := mul(r1, m2)
            mm := mulmod(r1, m2, not(0))
            let hi02 := sub(sub(mm, lo02), lt(mm, lo02))

            let lo10 := mul(r2, m0)
            mm := mulmod(r2, m0, not(0))
            let hi10 := sub(sub(mm, lo10), lt(mm, lo10))

            let lo11 := mul(r2, m1)
            mm := mulmod(r2, m1, not(0))
            let hi11 := sub(sub(mm, lo11), lt(mm, lo11))

            let lo12 := mul(r2, m2)
            mm := mulmod(r2, m2, not(0))
            let hi12 := sub(sub(mm, lo12), lt(mm, lo12))

            let limb := add(hi00, lo01)
            let carry := lt(limb, hi00)
            limb := add(limb, lo10)
            carry := add(carry, lt(limb, lo10))

            limb := add(hi01, hi10)
            let nextCarry := lt(limb, hi01)
            limb := add(limb, lo02)
            nextCarry := add(nextCarry, lt(limb, lo02))
            limb := add(limb, lo11)
            nextCarry := add(nextCarry, lt(limb, lo11))
            limb := add(limb, carry)
            nextCarry := add(nextCarry, lt(limb, carry))

            qLo := add(hi02, hi11)
            carry := lt(qLo, hi02)
            qLo := add(qLo, lo12)
            carry := add(carry, lt(qLo, lo12))
            qLo := add(qLo, nextCarry)
            carry := add(carry, lt(qLo, nextCarry))
            qHi := add(hi12, carry)
        }

        let pHi := 0x1a0111ea397fe69a4b1ba7b6434bacd7
        let pLo := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

        // Subtract the low two words of q*p. The Barrett bound gives a
        // nonnegative remainder below 3p, so two corrections are sufficient.
        {
            let productLo := mul(qLo, pLo)
            let mm := mulmod(qLo, pLo, not(0))
            let productHi := sub(sub(mm, productLo), lt(mm, productLo))
            productHi := add(add(productHi, mul(qLo, pHi)), mul(qHi, pLo))

            zLo := sub(r0, productLo)
            zHi := sub(sub(r1, productHi), lt(r0, productLo))
        }

        if fpGeModulus(zHi, zLo) {
            let nextLo := sub(zLo, pLo)
            zHi := sub(sub(zHi, pHi), gt(pLo, zLo))
            zLo := nextLo
        }
        if fpGeModulus(zHi, zLo) {
            let nextLo := sub(zLo, pLo)
            zHi := sub(sub(zHi, pHi), gt(pLo, zLo))
            zLo := nextLo
        }

    }

    // Two-limb CIOS Montgomery multiplication, with R = 2^512. Inputs and
    // output are canonical low/high word pairs.
    function montMul2(xLo, xHi, yLo, yHi) -> zLo, zHi {
        let t0 := 0
        let t1 := 0
        let t2 := 0

        {
            let lo := mul(xLo, yLo)
            let mm := mulmod(xLo, yLo, not(0))
            let hi := sub(sub(mm, lo), lt(mm, lo))
            t0 := lo
            let carry := hi

            lo := mul(xLo, yHi)
            mm := mulmod(xLo, yHi, not(0))
            hi := sub(sub(mm, lo), lt(mm, lo))
            let sum := add(lo, carry)
            t1 := sum
            t2 := add(hi, lt(sum, lo))
        }

        let factor := mul(t0,
            0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd)
        {
            let pLo := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
            let lo := mul(factor, pLo)
            let mm := mulmod(factor, pLo, not(0))
            let hi := sub(sub(mm, lo), lt(mm, lo))
            let sum := add(t0, lo)
            let carry := add(hi, lt(sum, t0))

            let pHi := 0x1a0111ea397fe69a4b1ba7b6434bacd7
            lo := mul(factor, pHi)
            mm := mulmod(factor, pHi, not(0))
            hi := sub(sub(mm, lo), lt(mm, lo))
            sum := add(t1, lo)
            let carry1 := lt(sum, t1)
            let sum2 := add(sum, carry)
            let carry2 := lt(sum2, sum)
            t0 := sum2
            t1 := add(t2, add(hi, add(carry1, carry2)))
            t2 := 0
        }

        {
            let lo := mul(xHi, yLo)
            let mm := mulmod(xHi, yLo, not(0))
            let hi := sub(sub(mm, lo), lt(mm, lo))
            let sum := add(t0, lo)
            let carry := add(hi, lt(sum, t0))
            t0 := sum

            lo := mul(xHi, yHi)
            mm := mulmod(xHi, yHi, not(0))
            hi := sub(sub(mm, lo), lt(mm, lo))
            sum := add(t1, lo)
            let carry1 := lt(sum, t1)
            let sum2 := add(sum, carry)
            let carry2 := lt(sum2, sum)
            t1 := sum2
            t2 := add(hi, add(carry1, carry2))
        }

        factor := mul(t0,
            0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd)
        {
            let pLo := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
            let lo := mul(factor, pLo)
            let mm := mulmod(factor, pLo, not(0))
            let hi := sub(sub(mm, lo), lt(mm, lo))
            let sum := add(t0, lo)
            let carry := add(hi, lt(sum, t0))

            let pHi := 0x1a0111ea397fe69a4b1ba7b6434bacd7
            lo := mul(factor, pHi)
            mm := mulmod(factor, pHi, not(0))
            hi := sub(sub(mm, lo), lt(mm, lo))
            sum := add(t1, lo)
            let carry1 := lt(sum, t1)
            let sum2 := add(sum, carry)
            let carry2 := lt(sum2, sum)
            zLo := sum2
            zHi := add(t2, add(hi, add(carry1, carry2)))
        }

        if fpGeModulus(zHi, zLo) {
            let pHi := 0x1a0111ea397fe69a4b1ba7b6434bacd7
            let pLo := 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
            let nextLo := sub(zLo, pLo)
            zHi := sub(sub(zHi, pHi), gt(pLo, zLo))
            zLo := nextLo
        }
    }

}
