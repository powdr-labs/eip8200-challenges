// SPDX-License-Identifier: Apache-2.0
// Proof-friendly naive EIP-2537 G1ADD.
//
// Field elements are carried as (high128, low256) words. Multiplication uses
// an exact three-word schoolbook product and the MODEXP precompile with
// exponent one for reduction. Inversion uses MODEXP with exponent p-2.
// Only native G1ADD is disabled by the challenge execution profile.
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

        // MODEXP(base = r2:r1:r0, exponent = 1, modulus = p).
        mstore(0x400, 96)
        mstore(0x420, 1)
        mstore(0x440, 48)
        mstore(0x460, r2)
        mstore(0x480, r1)
        mstore(0x4a0, r0)
        mstore8(0x4c0, 1)
        storeModulus(0x4c1)
        // The exact Osaka MODEXP charge for these lengths and exponent is 500.
        if iszero(staticcall(500, 5, 0x400, 241, 0x500, 48)) { invalid() }
        zHi := shr(128, mload(0x500))
        zLo := mload(0x510)
    }

    function fpInv(aHi, aLo) -> zHi, zLo {
        // MODEXP(base = a, exponent = p-2, modulus = p).
        mstore(0x400, 48)
        mstore(0x420, 48)
        mstore(0x440, 48)
        storeFp(0x460, aHi, aLo)
        storeFp(
            0x490,
            0x1a0111ea397fe69a4b1ba7b6434bacd7,
            0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaa9
        )
        storeModulus(0x4c0)
        // The exact Osaka MODEXP charge for these lengths and p-2 is 36,576.
        if iszero(staticcall(36576, 5, 0x400, 240, 0x500, 48)) { invalid() }
        zHi := shr(128, mload(0x500))
        zLo := mload(0x510)
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
}
