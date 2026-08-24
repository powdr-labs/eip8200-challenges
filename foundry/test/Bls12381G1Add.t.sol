// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {YulArtifact} from "../src/YulArtifact.sol";

/// @notice Differential checks for the compiled, test-only G1ADD Yul artifact.
contract Bls12381G1AddTest is Test {
    address internal constant NATIVE_G1ADD = address(0x0b);
    address internal constant REFERENCE = address(0x820b);

    bytes internal constant GENERATOR = hex"00000000000000000000000000000000"
        hex"17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac58"
        hex"6c55e83ff97a1aeffb3af00adb22c6bb" hex"00000000000000000000000000000000"
        hex"08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3ed"
        hex"d03cc744a2888ae40caa232946c5e7e1";

    function setUp() public {
        vm.etch(REFERENCE, YulArtifact.load(vm, "../Challenge/Bls12381G1Add/Reference"));
    }

    function _assertMatchesNative(bytes memory input, string memory label) private view {
        // Invalid precompile inputs consume all forwarded gas. Bound both calls
        // so negative vectors cannot consume the surrounding test frame.
        (bool expectedOk, bytes memory expected) = NATIVE_G1ADD.staticcall{gas: 1_000_000}(input);
        (bool actualOk, bytes memory actual) = REFERENCE.staticcall{gas: 1_000_000}(input);
        assertEq(actualOk, expectedOk, string.concat(label, ": success"));
        assertEq(actual, expected, string.concat(label, ": output"));
    }

    function _zeroPoint() private pure returns (bytes memory) {
        return new bytes(128);
    }

    function test_compiled_artifact_is_present() public view {
        assertEq(REFERENCE.code.length, 4687, "automatic yul-compiler artifact size");
    }

    function _contains(bytes memory haystack, bytes memory needle) private pure returns (bool) {
        if (needle.length > haystack.length) return false;
        for (uint256 i = 0; i + needle.length <= haystack.length; i++) {
            bool equal = true;
            for (uint256 j = 0; j < needle.length; j++) {
                if (haystack[i + j] != needle[j]) {
                    equal = false;
                    break;
                }
            }
            if (equal) return true;
        }
        return false;
    }

    function test_reference_source_has_no_external_operations() public view {
        bytes memory source = bytes(vm.readFile("../Challenge/Bls12381G1Add/Reference/reference.yul"));
        assertFalse(_contains(source, bytes("call(")), "CALL is forbidden");
        assertFalse(_contains(source, bytes("callcode(")), "CALLCODE is forbidden");
        assertFalse(_contains(source, bytes("delegatecall(")), "DELEGATECALL is forbidden");
        assertFalse(_contains(source, bytes("staticcall(")), "STATICCALL is forbidden");
        assertFalse(_contains(source, bytes("create(")), "CREATE is forbidden");
        assertFalse(_contains(source, bytes("create2(")), "CREATE2 is forbidden");
    }

    function test_infinity_plus_infinity() public view {
        _assertMatchesNative(abi.encodePacked(_zeroPoint(), _zeroPoint()), "infinity + infinity");
    }

    function test_generator_plus_infinity() public view {
        _assertMatchesNative(abi.encodePacked(GENERATOR, _zeroPoint()), "generator + infinity");
    }

    function test_generator_doubling() public view {
        _assertMatchesNative(abi.encodePacked(GENERATOR, GENERATOR), "generator doubling");
    }

    function test_generator_plus_double_generator() public view {
        (bool ok, bytes memory doubled) =
            NATIVE_G1ADD.staticcall{gas: 1_000_000}(abi.encodePacked(GENERATOR, GENERATOR));
        assertTrue(ok, "native generator doubling");
        _assertMatchesNative(abi.encodePacked(GENERATOR, doubled), "generator + doubled generator");
    }

    function test_rejects_malformed_inputs() public view {
        bytes memory wrongLength = new bytes(255);
        _assertMatchesNative(wrongLength, "wrong length");

        bytes memory nonzeroPadding = abi.encodePacked(_zeroPoint(), _zeroPoint());
        nonzeroPadding[0] = 0x01;
        _assertMatchesNative(nonzeroPadding, "nonzero field padding");

        bytes memory offCurve = abi.encodePacked(_zeroPoint(), _zeroPoint());
        offCurve[63] = 0x01;
        offCurve[127] = 0x01;
        _assertMatchesNative(offCurve, "off-curve point");
    }
}
