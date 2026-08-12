// SPDX-License-Identifier: Apache-2.0
// Proof-friendly naive EIP-2537 G1MSM.
//
// Field elements use (high128, low256) words. The concrete scalar schedule is
// a fixed 256-bit MSB-first double-and-add loop; MSM is a left fold. Both the
// subgroup check and requested scalar multiplication deliberately use this
// same naive routine. Only native G1MSM is disabled by the challenge profile.
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

        mstore(0x400, 96)
        mstore(0x420, 1)
        mstore(0x440, 48)
        mstore(0x460, r2)
        mstore(0x480, r1)
        mstore(0x4a0, r0)
        mstore8(0x4c0, 1)
        storeModulus(0x4c1)
        if iszero(staticcall(500, 5, 0x400, 241, 0x500, 48)) { invalid() }
        zHi := shr(128, mload(0x500))
        zLo := mload(0x510)
    }

    function fpInv(aHi, aLo) -> zHi, zLo {
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

    function storePoint(ptr, xHi, xLo, yHi, yLo) {
        mstore(ptr, xHi)
        mstore(add(ptr, 32), xLo)
        mstore(add(ptr, 64), yHi)
        mstore(add(ptr, 96), yLo)
    }

    function storeInfinity(ptr) {
        storePoint(ptr, 0, 0, 0, 0)
    }

    function copyPoint(dst, src) {
        storePoint(
            dst,
            mload(src),
            mload(add(src, 32)),
            mload(add(src, 64)),
            mload(add(src, 96))
        )
    }

    function pointInfinity(ptr) -> yes {
        yes := and(
            fpZero(mload(ptr), mload(add(ptr, 32))),
            fpZero(mload(add(ptr, 64)), mload(add(ptr, 96)))
        )
    }

    // Alias-safe lawful affine addition. All inputs are loaded before the
    // final store in each finite branch, so out may equal left or right.
    function pointAdd(out, left, right) {
        // Consume the pointer parameters before entering arithmetic helpers.
        // Keeping all three live across nested field calls exceeds the EVM's
        // pre-EIP-8024 stack-depth rule even though the values are just fixed
        // memory addresses.
        mstore(0x600, out)
        mstore(0x620, left)
        mstore(0x640, right)

        if pointInfinity(mload(0x620)) {
            copyPoint(mload(0x600), mload(0x640))
            leave
        }
        if pointInfinity(mload(0x640)) {
            copyPoint(mload(0x600), mload(0x620))
            leave
        }

        if fpEq(
            mload(mload(0x620)), mload(add(mload(0x620), 32)),
            mload(mload(0x640)), mload(add(mload(0x640), 32))
        ) {
            let sumHi, sumLo := fpAdd(
                mload(add(mload(0x620), 64)), mload(add(mload(0x620), 96)),
                mload(add(mload(0x640), 64)), mload(add(mload(0x640), 96))
            )
            if fpZero(sumHi, sumLo) {
                storeInfinity(mload(0x600))
                leave
            }

            let xSqHi, xSqLo := fpMul(
                mload(mload(0x620)), mload(add(mload(0x620), 32)),
                mload(mload(0x620)), mload(add(mload(0x620), 32))
            )
            let numHi, numLo := fpAdd(xSqHi, xSqLo, xSqHi, xSqLo)
            numHi, numLo := fpAdd(numHi, numLo, xSqHi, xSqLo)
            let denHi, denLo := fpAdd(
                mload(add(mload(0x620), 64)), mload(add(mload(0x620), 96)),
                mload(add(mload(0x620), 64)), mload(add(mload(0x620), 96))
            )
            let denInvHi, denInvLo := fpInv(denHi, denLo)
            let lamHi, lamLo := fpMul(numHi, numLo, denInvHi, denInvLo)
            let x3Hi, x3Lo := fpMul(lamHi, lamLo, lamHi, lamLo)
            x3Hi, x3Lo := fpSub(
                x3Hi, x3Lo,
                mload(mload(0x620)), mload(add(mload(0x620), 32))
            )
            x3Hi, x3Lo := fpSub(
                x3Hi, x3Lo,
                mload(mload(0x640)), mload(add(mload(0x640), 32))
            )
            let deltaHi, deltaLo := fpSub(
                mload(mload(0x620)), mload(add(mload(0x620), 32)), x3Hi, x3Lo
            )
            let y3Hi, y3Lo := fpMul(lamHi, lamLo, deltaHi, deltaLo)
            y3Hi, y3Lo := fpSub(
                y3Hi, y3Lo,
                mload(add(mload(0x620), 64)), mload(add(mload(0x620), 96))
            )
            storePoint(mload(0x600), x3Hi, x3Lo, y3Hi, y3Lo)
            leave
        }

        let numHi, numLo := fpSub(
            mload(add(mload(0x640), 64)), mload(add(mload(0x640), 96)),
            mload(add(mload(0x620), 64)), mload(add(mload(0x620), 96))
        )
        let denHi, denLo := fpSub(
            mload(mload(0x640)), mload(add(mload(0x640), 32)),
            mload(mload(0x620)), mload(add(mload(0x620), 32))
        )
        let denInvHi, denInvLo := fpInv(denHi, denLo)
        let lamHi, lamLo := fpMul(numHi, numLo, denInvHi, denInvLo)
        let x3Hi, x3Lo := fpMul(lamHi, lamLo, lamHi, lamLo)
        x3Hi, x3Lo := fpSub(
            x3Hi, x3Lo,
            mload(mload(0x620)), mload(add(mload(0x620), 32))
        )
        x3Hi, x3Lo := fpSub(
            x3Hi, x3Lo,
            mload(mload(0x640)), mload(add(mload(0x640), 32))
        )
        let deltaHi, deltaLo := fpSub(
            mload(mload(0x620)), mload(add(mload(0x620), 32)), x3Hi, x3Lo
        )
        let y3Hi, y3Lo := fpMul(lamHi, lamLo, deltaHi, deltaLo)
        y3Hi, y3Lo := fpSub(
            y3Hi, y3Lo,
            mload(add(mload(0x620), 64)), mload(add(mload(0x620), 96))
        )
        storePoint(mload(0x600), x3Hi, x3Lo, y3Hi, y3Lo)
    }

    function scalarMul(scalar, point, out) {
        storeInfinity(out)
        let bit := shl(255, 1)
        for { } bit { bit := shr(1, bit) } {
            pointAdd(out, out, out)
            if and(scalar, bit) {
                pointAdd(out, out, point)
            }
        }
    }

    let size := calldatasize()
    if or(iszero(size), mod(size, 160)) { invalid() }

    let point := 0x800
    let subgroupOut := 0x880
    let termOut := 0x900
    let acc := 0x980
    storeInfinity(acc)

    for { let offset := 0 } lt(offset, size) { offset := add(offset, 160) } {
        mstore(point, calldataload(offset))
        mstore(add(point, 32), calldataload(add(offset, 32)))
        mstore(add(point, 64), calldataload(add(offset, 64)))
        mstore(add(point, 96), calldataload(add(offset, 96)))

        if or(shr(128, mload(point)), shr(128, mload(add(point, 64)))) {
            invalid()
        }
        if iszero(and(
            fpValid(mload(point), mload(add(point, 32))),
            fpValid(mload(add(point, 64)), mload(add(point, 96)))
        )) { invalid() }
        if and(iszero(pointInfinity(point)), iszero(onCurve(
            mload(point), mload(add(point, 32)),
            mload(add(point, 64)), mload(add(point, 96))
        ))) { invalid() }

        scalarMul(
            0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001,
            point,
            subgroupOut
        )
        if iszero(pointInfinity(subgroupOut)) { invalid() }

        scalarMul(calldataload(add(offset, 128)), point, termOut)
        pointAdd(acc, acc, termOut)
    }

    copyPoint(0, acc)
    return(0, 128)
}
