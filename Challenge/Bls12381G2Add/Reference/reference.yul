// SPDX-License-Identifier: Apache-2.0
// Proof-friendly naive EIP-2537 G2ADD.
//
// An Fp value is (high128, low256); an Fp2 value is four consecutive memory
// words (c0.high, c0.low, c1.high, c1.low).  Fp multiplication and inversion
// use fixed-size MODEXP calls.  Fp2 and affine G2 operations deliberately use
// the simple formulas mirrored by the shared proof-support layer.
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

    function fp2Valid(a) -> yes {
        yes := and(
            fpValid(mload(a), mload(add(a, 32))),
            fpValid(mload(add(a, 64)), mload(add(a, 96)))
        )
    }

    function fp2Zero(a) -> yes {
        yes := and(
            fpZero(mload(a), mload(add(a, 32))),
            fpZero(mload(add(a, 64)), mload(add(a, 96)))
        )
    }

    function fp2Eq(a, b) -> yes {
        yes := and(
            fpEq(mload(a), mload(add(a, 32)), mload(b), mload(add(b, 32))),
            fpEq(mload(add(a, 64)), mload(add(a, 96)),
                 mload(add(b, 64)), mload(add(b, 96)))
        )
    }

    function fp2Add(out, a, b) {
        let zHi, zLo := fpAdd(
            mload(a), mload(add(a, 32)), mload(b), mload(add(b, 32)))
        mstore(out, zHi)
        mstore(add(out, 32), zLo)
        zHi, zLo := fpAdd(
            mload(add(a, 64)), mload(add(a, 96)),
            mload(add(b, 64)), mload(add(b, 96)))
        mstore(add(out, 64), zHi)
        mstore(add(out, 96), zLo)
    }

    function fp2Sub(out, a, b) {
        let zHi, zLo := fpSub(
            mload(a), mload(add(a, 32)), mload(b), mload(add(b, 32)))
        mstore(out, zHi)
        mstore(add(out, 32), zLo)
        zHi, zLo := fpSub(
            mload(add(a, 64)), mload(add(a, 96)),
            mload(add(b, 64)), mload(add(b, 96)))
        mstore(add(out, 64), zHi)
        mstore(add(out, 96), zLo)
    }

    // Karatsuba Fp2 multiplication. Scratch 0x600..0x77f is private to this
    // helper; callers keep persistent values at 0x800 and above.
    function fp2Mul(out, a, b) {
        let zHi, zLo := fpMul(
            mload(a), mload(add(a, 32)), mload(b), mload(add(b, 32)))
        mstore(0x600, zHi)
        mstore(0x620, zLo)

        zHi, zLo := fpMul(
            mload(add(a, 64)), mload(add(a, 96)),
            mload(add(b, 64)), mload(add(b, 96)))
        mstore(0x640, zHi)
        mstore(0x660, zLo)

        zHi, zLo := fpSub(mload(0x600), mload(0x620), mload(0x640), mload(0x660))
        mstore(out, zHi)
        mstore(add(out, 32), zLo)

        zHi, zLo := fpAdd(
            mload(a), mload(add(a, 32)), mload(add(a, 64)), mload(add(a, 96)))
        mstore(0x680, zHi)
        mstore(0x6a0, zLo)
        zHi, zLo := fpAdd(
            mload(b), mload(add(b, 32)), mload(add(b, 64)), mload(add(b, 96)))
        mstore(0x6c0, zHi)
        mstore(0x6e0, zLo)

        zHi, zLo := fpMul(
            mload(0x680), mload(0x6a0), mload(0x6c0), mload(0x6e0))
        mstore(0x700, zHi)
        mstore(0x720, zLo)
        zHi, zLo := fpAdd(
            mload(0x600), mload(0x620), mload(0x640), mload(0x660))
        mstore(0x740, zHi)
        mstore(0x760, zLo)
        zHi, zLo := fpSub(
            mload(0x700), mload(0x720), mload(0x740), mload(0x760))
        mstore(add(out, 64), zHi)
        mstore(add(out, 96), zLo)
    }

    // (a0 + a1*u)^-1 = (a0 - a1*u)/(a0^2 + a1^2), with u^2 = -1.
    function fp2Inv(out, a) {
        let zHi, zLo := fpMul(
            mload(a), mload(add(a, 32)), mload(a), mload(add(a, 32)))
        mstore(0x600, zHi)
        mstore(0x620, zLo)
        zHi, zLo := fpMul(
            mload(add(a, 64)), mload(add(a, 96)),
            mload(add(a, 64)), mload(add(a, 96)))
        mstore(0x640, zHi)
        mstore(0x660, zLo)
        zHi, zLo := fpAdd(
            mload(0x600), mload(0x620), mload(0x640), mload(0x660))
        zHi, zLo := fpInv(zHi, zLo)
        mstore(0x680, zHi)
        mstore(0x6a0, zLo)

        zHi, zLo := fpMul(
            mload(a), mload(add(a, 32)), mload(0x680), mload(0x6a0))
        mstore(out, zHi)
        mstore(add(out, 32), zLo)

        zHi, zLo := fpSub(0, 0, mload(add(a, 64)), mload(add(a, 96)))
        zHi, zLo := fpMul(zHi, zLo, mload(0x680), mload(0x6a0))
        mstore(add(out, 64), zHi)
        mstore(add(out, 96), zLo)
    }

    function onCurve(x, y) -> yes {
        fp2Mul(0x800, y, y)
        fp2Mul(0x880, x, x)
        fp2Mul(0x900, 0x880, x)

        // Twist coefficient 4*(1+u).
        mstore(0x980, 0)
        mstore(0x9a0, 4)
        mstore(0x9c0, 0)
        mstore(0x9e0, 4)
        fp2Add(0x900, 0x900, 0x980)
        yes := fp2Eq(0x800, 0x900)
    }

    function pointPaddingZero(point) -> yes {
        yes := iszero(or(
            or(shr(128, mload(point)), shr(128, mload(add(point, 64)))),
            or(shr(128, mload(add(point, 128))), shr(128, mload(add(point, 192))))
        ))
    }

    function pointValid(point) -> yes {
        yes := and(
            and(fp2Valid(point), fp2Valid(add(point, 128))),
            pointPaddingZero(point)
        )
    }

    function pointZero(point) -> yes {
        yes := and(fp2Zero(point), fp2Zero(add(point, 128)))
    }

    function clearPoint() {
        mstore(0, 0)
        mstore(32, 0)
        mstore(64, 0)
        mstore(96, 0)
        mstore(128, 0)
        mstore(160, 0)
        mstore(192, 0)
        mstore(224, 0)
    }

    function copyPoint(point) {
        mstore(0, mload(point))
        mstore(32, mload(add(point, 32)))
        mstore(64, mload(add(point, 64)))
        mstore(96, mload(add(point, 96)))
        mstore(128, mload(add(point, 128)))
        mstore(160, mload(add(point, 160)))
        mstore(192, mload(add(point, 192)))
        mstore(224, mload(add(point, 224)))
    }

    function storePoint(x, y) {
        mstore(0, mload(x))
        mstore(32, mload(add(x, 32)))
        mstore(64, mload(add(x, 64)))
        mstore(96, mload(add(x, 96)))
        mstore(128, mload(y))
        mstore(160, mload(add(y, 32)))
        mstore(192, mload(add(y, 64)))
        mstore(224, mload(add(y, 96)))
    }

    if iszero(eq(calldatasize(), 512)) { invalid() }

    // Stage both points at 0x000 and 0x100. Each EIP field element is two
    // 32-byte words: a zero-padded high half followed by the low word.
    mstore(0, calldataload(0))
    mstore(32, calldataload(32))
    mstore(64, calldataload(64))
    mstore(96, calldataload(96))
    mstore(128, calldataload(128))
    mstore(160, calldataload(160))
    mstore(192, calldataload(192))
    mstore(224, calldataload(224))
    mstore(256, calldataload(256))
    mstore(288, calldataload(288))
    mstore(320, calldataload(320))
    mstore(352, calldataload(352))
    mstore(384, calldataload(384))
    mstore(416, calldataload(416))
    mstore(448, calldataload(448))
    mstore(480, calldataload(480))

    if iszero(and(pointValid(0), pointValid(256))) { invalid() }

    {
        let inf1 := pointZero(0)
        let inf2 := pointZero(256)
        if and(iszero(inf1), iszero(onCurve(0, 128))) { invalid() }
        if and(iszero(inf2), iszero(onCurve(256, 384))) { invalid() }

        if and(inf1, inf2) { clearPoint() return(0, 256) }
        if inf1 { copyPoint(256) return(0, 256) }
        if inf2 { return(0, 256) }
    }

    // Persistent affine intermediates start at 0x800. Fp2 helpers use only
    // 0x600..0x77f as private arithmetic scratch.
    if fp2Eq(0, 256) {
        if iszero(fp2Eq(128, 384)) { clearPoint() return(0, 256) }
        if fp2Zero(128) { clearPoint() return(0, 256) }

        fp2Mul(0x880, 0, 0)
        fp2Add(0x900, 0x880, 0x880)
        fp2Add(0x900, 0x900, 0x880)
        fp2Add(0x980, 128, 128)
        fp2Inv(0xa00, 0x980)
        fp2Mul(0x800, 0x900, 0xa00)
    }
    if iszero(fp2Eq(0, 256)) {
        fp2Sub(0x900, 384, 128)
        fp2Sub(0x980, 256, 0)
        fp2Inv(0xa00, 0x980)
        fp2Mul(0x800, 0x900, 0xa00)
    }

    fp2Mul(0xa80, 0x800, 0x800)
    fp2Sub(0xa80, 0xa80, 0)
    fp2Sub(0xa80, 0xa80, 256)
    fp2Sub(0xb00, 0, 0xa80)
    fp2Mul(0xb80, 0x800, 0xb00)
    fp2Sub(0xb80, 0xb80, 128)
    storePoint(0xa80, 0xb80)
    return(0, 256)
}
