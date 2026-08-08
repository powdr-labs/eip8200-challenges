// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {console2} from "forge-std/Test.sol";
import {GasCrossCheck} from "./GasCrossCheck.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {Blake2fDeployed} from "evmification/blake2f/Blake2fDeployed.sol";

/// @notice Independent revm cross-check of the BLAKE2f challenge reference.
contract Blake2fGasTest is GasCrossCheck {
    Case[] internal cases;
    address internal refAddr;
    address internal evmification;

    bytes internal constant H = hex"48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
        hex"d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b";

    function _input(uint32 rounds, uint8 flag) private pure returns (bytes memory out) {
        out = new bytes(213);
        out[0] = bytes1(uint8(rounds >> 24));
        out[1] = bytes1(uint8(rounds >> 16));
        out[2] = bytes1(uint8(rounds >> 8));
        out[3] = bytes1(uint8(rounds));
        for (uint256 i = 0; i < H.length; i++) {
            out[4 + i] = H[i];
        }
        out[68] = "a";
        out[69] = "b";
        out[70] = "c";
        out[196] = bytes1(uint8(3));
        out[212] = bytes1(flag);
    }

    function _truncate(bytes memory input, uint256 len) private pure returns (bytes memory out) {
        out = new bytes(len);
        for (uint256 i = 0; i < len; i++) {
            out[i] = input[i];
        }
    }

    function setUp() public override {
        super.setUp();
        refAddr = _etchReferenceAt("../Challenge/Blake2f/Reference", address(uint160(0x8209)));
        evmification = address(new Blake2fDeployed());

        cases.push(Case("0 rounds, f=0", _input(0, 0), 29213));
        cases.push(Case("0 rounds, f=1", _input(0, 1), 29231));
        cases.push(Case("1 round", _input(1, 1), 33201));
        cases.push(Case("2 rounds", _input(2, 1), 37171));
        cases.push(Case("9 rounds", _input(9, 1), 64961));
        cases.push(Case("10 rounds", _input(10, 1), 68931));
        cases.push(Case("11 rounds", _input(11, 1), 72901));
        cases.push(Case("12 rounds, f=0", _input(12, 0), 76853));
        cases.push(Case("12 rounds, f=1", _input(12, 1), 76871));
        cases.push(Case("100 rounds", _input(100, 1), 426231));
        cases.push(Case("212-byte invalid", _truncate(_input(12, 1), 212), 57));
        cases.push(Case("214-byte invalid", abi.encodePacked(_input(12, 1), bytes1(0)), 57));
        cases.push(Case("flag=2 invalid", _input(12, 2), 94));
    }

    function test_vectors_match_scorer() public view {
        assertEq(cases.length, 13, "vector count");
        assertEq(pin.provedSize, 1169, "reference bytecode size");
        assertEq(refAddr.code.length, 1169, "etched code size");
        for (uint256 i = 0; i < 10; i++) {
            assertEq(cases[i].input.length, 213, cases[i].label);
        }
        assertEq(cases[10].input.length, 212);
        assertEq(cases[11].input.length, 214);
        assertEq(cases[12].input.length, 213);
    }

    function test_reference_matches_precompile() public view {
        for (uint256 i = 0; i < 10; i++) {
            (, bytes memory actual) = _gas(refAddr, cases[i].input);
            (, bytes memory expected) = _gas(address(0x09), cases[i].input);
            assertEq(actual, expected, cases[i].label);
            assertEq(actual.length, 64, cases[i].label);
        }
    }

    function test_reference_rejects_malformed_inputs() public view {
        for (uint256 i = 10; i < cases.length; i++) {
            GasProbe.Result memory result = GasProbe.probe(refAddr, cases[i].input);
            assertFalse(result.ok, cases[i].label);
        }
    }

    function test_reference_gas_matches_lean_scorer() public view {
        uint256 leanTotal;
        uint256 forgeTotal;
        _header("BLAKE2f reference: Lean scorer vs revm");
        // Exceptional callees consume all gas forwarded by STATICCALL, so a
        // caller-side probe cannot recover the 57/94 gas spent before INVALID.
        // The three malformed vectors are checked for failure above; this
        // independent exact-gas comparison covers every successful vector.
        for (uint256 i = 0; i < 10; i++) {
            GasProbe.Result memory result = GasProbe.probe(refAddr, cases[i].input);
            _row(cases[i].label, cases[i].input.length, cases[i].leanGas, result.gasUsed);
            assertEq(result.gasUsed, cases[i].leanGas, cases[i].label);
            leanTotal += cases[i].leanGas;
            forgeTotal += result.gasUsed;
        }
        _row("all vectors", 0, leanTotal, forgeTotal);
        assertEq(forgeTotal, 915564, "README valid-vector total");
    }

    function test_valid_input_precompile_ratio() public view {
        uint256 referenceTotal;
        uint256 precompileTotal;
        for (uint256 i = 0; i < 10; i++) {
            (uint256 referenceGas,) = _gas(refAddr, cases[i].input);
            (uint256 precompileGas,) = _gas(address(0x09), cases[i].input);
            assertEq(precompileGas, uint32(bytes4(cases[i].input)), "round-priced precompile");
            referenceTotal += referenceGas;
            precompileTotal += precompileGas;
        }
        assertEq(referenceTotal, 915564, "valid reference total");
        assertEq(precompileTotal, 157, "valid precompile total");
        assertEq(_ratio(referenceTotal, precompileTotal), "5831.62x", "vs precompile ratio");
    }

    function test_evmification_comparison() public view {
        uint256 referenceTotal;
        uint256 evmificationTotal;
        for (uint256 i = 0; i < 10; i++) {
            (uint256 referenceGas, bytes memory expected) = _gas(refAddr, cases[i].input);
            (uint256 implementationGas, bytes memory actual) = _gas(evmification, cases[i].input);
            assertEq(actual, expected, cases[i].label);
            referenceTotal += referenceGas;
            evmificationTotal += implementationGas;
        }
        console2.log(string.concat("reference vs evmification: ", _ratio(referenceTotal, evmificationTotal)));
    }

    function test_gas_is_state_independent() public {
        _assertGasIsStateIndependent(refAddr, cases[0].input, "0 rounds");
        _assertGasIsStateIndependent(refAddr, cases[9].input, "100 rounds");
    }
}
