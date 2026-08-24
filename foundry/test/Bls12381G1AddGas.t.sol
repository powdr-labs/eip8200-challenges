// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Test, console2} from "forge-std/Test.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {YulArtifact} from "../src/YulArtifact.sol";

/// @notice Reproducible frame-gas measurements for the generated G1ADD artifact.
/// @dev These are artifact tests, not Lean theorems: correctness is proved for
///      the parsed Yul source and is deliberately not transported to bytecode.
contract Bls12381G1AddGasTest is Test {
    address internal constant NATIVE_G1ADD = address(0x0b);
    address internal constant REFERENCE = address(0x820b);
    uint256 internal constant PROBE_GAS_LIMIT = 1_000_000;

    bytes internal constant GENERATOR = hex"00000000000000000000000000000000"
        hex"17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac58"
        hex"6c55e83ff97a1aeffb3af00adb22c6bb" hex"00000000000000000000000000000000"
        hex"08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3ed"
        hex"d03cc744a2888ae40caa232946c5e7e1";

    bytes internal constant NEG_GENERATOR = hex"00000000000000000000000000000000"
        hex"17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac58"
        hex"6c55e83ff97a1aeffb3af00adb22c6bb" hex"00000000000000000000000000000000"
        hex"114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac4236"
        hex"4e6f38ba0ecb751bad54dcd6b939c2ca";

    bytes internal constant DOUBLE_GENERATOR = hex"00000000000000000000000000000000"
        hex"0572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62a"
        hex"e28f75bb8f1c7c42c39a8c5529bf0f4e" hex"00000000000000000000000000000000"
        hex"166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a"
        hex"4c56d9d4cd16bd1bba86881979749d28";

    struct Case {
        string label;
        bytes input;
        uint256 expectedGas;
    }

    Case[] internal cases;

    function setUp() public {
        vm.etch(GasProbe.STOP_TARGET, hex"00");
        vm.etch(REFERENCE, YulArtifact.load(vm, "../Challenge/Bls12381G1Add/Reference"));

        bytes memory infinity = new bytes(128);
        cases.push(Case("infinity + infinity", abi.encodePacked(infinity, infinity), 11_850));
        cases.push(Case("generator + infinity", abi.encodePacked(GENERATOR, infinity), 11_880));
        cases.push(Case("infinity + generator", abi.encodePacked(infinity, GENERATOR), 11_912));
        cases.push(Case("generator + negative", abi.encodePacked(GENERATOR, NEG_GENERATOR), 12_160));
        cases.push(Case("generator doubling", abi.encodePacked(GENERATOR, GENERATOR), 702_066));
        cases.push(Case("generator + double", abi.encodePacked(GENERATOR, DOUBLE_GENERATOR), 699_670));
    }

    function test_report() public view {
        assertEq(cases.length, 6, "report vector count");
        assertEq(REFERENCE.code.length, 4_687, "automatic yul-compiler artifact size");

        uint256 referenceTotal;
        uint256 nativeTotal;

        for (uint256 i = 0; i < cases.length; i++) {
            GasProbe.Result memory refResult =
                GasProbe.probeCapped(REFERENCE, cases[i].input, PROBE_GAS_LIMIT);
            GasProbe.Result memory native =
                GasProbe.probeCapped(NATIVE_G1ADD, cases[i].input, PROBE_GAS_LIMIT);

            assertTrue(refResult.ok, string.concat(cases[i].label, ": reference success"));
            assertTrue(native.ok, string.concat(cases[i].label, ": native success"));
            assertEq(refResult.ret, native.ret, string.concat(cases[i].label, ": output"));
            assertEq(native.gasUsed, 375, string.concat(cases[i].label, ": native gas"));
            assertEq(refResult.gasUsed, cases[i].expectedGas, string.concat(cases[i].label, ": gas"));
            if (i == 0 || i == 3) {
                assertEq(native.ret, new bytes(128), string.concat(cases[i].label, ": infinity"));
            }
            if (i == 1 || i == 2) {
                assertEq(native.ret, GENERATOR, string.concat(cases[i].label, ": identity"));
            }
            if (i == 4) assertEq(native.ret, DOUBLE_GENERATOR, "doubling fixture");

            console2.log(
                string.concat(
                    "BLS_GAS,",
                    cases[i].label,
                    ",",
                    vm.toString(cases[i].input.length),
                    ",",
                    vm.toString(refResult.gasUsed),
                    ",",
                    vm.toString(native.gasUsed)
                )
            );
            referenceTotal += refResult.gasUsed;
            nativeTotal += native.gasUsed;
        }

        console2.log(
            string.concat(
                "BLS_GAS_TOTAL,",
                vm.toString(cases.length),
                ",",
                vm.toString(REFERENCE.code.length),
                ",",
                vm.toString(referenceTotal),
                ",",
                vm.toString(nativeTotal)
            )
        );
        assertEq(referenceTotal, 1_449_538, "README reference total");
        assertEq(nativeTotal, 2_250, "README native total");
    }
}
