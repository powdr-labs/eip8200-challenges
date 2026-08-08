// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Test, console2} from "forge-std/Test.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {LeanArtifact} from "../src/LeanArtifact.sol";

/// @title GasCrossCheck
/// @notice Shared scaffolding for the challenge cross-checks.
///
/// @dev Each challenge test declares its vectors together with the gas its
///      `Scorer.lean` reports for them, etches the frozen reference artifact,
///      and asserts that a real EVM charges the same. The Lean numbers are
///      recorded here as constants and never recomputed by this suite, so the
///      comparison is between two independent implementations of the EVM's gas
///      rules rather than between two runs of the same one.
abstract contract GasCrossCheck is Test {
    /// @dev One scored vector: the label the Lean scorer prints, its calldata,
    ///      and the gas that scorer reports for the reference bytecode.
    struct Case {
        string label;
        bytes input;
        uint256 leanGas;
    }

    /// @dev `Spec.lean` fixes `deployAddress := AccountAddress.ofNat 0x8200`;
    ///      the cross-check runs the artifact at the same address.
    address internal constant REFERENCE_ADDRESS = address(uint160(0x8200));

    LeanArtifact.Pin internal pin;

    function setUp() public virtual {
        // Calibration target for GasProbe: a frame that consumes zero gas.
        vm.etch(GasProbe.STOP_TARGET, hex"00");
    }

    /// @notice Loads the frozen artifact from `referenceDir`, proving it is the
    ///         bytecode the Lean theorems are about, and etches it.
    function _etchReference(string memory referenceDir) internal returns (address) {
        return _etchReferenceAt(referenceDir, REFERENCE_ADDRESS);
    }

    /// @notice Variant for challenges whose specification pins another
    ///         non-precompile address.
    function _etchReferenceAt(string memory referenceDir, address target) internal returns (address) {
        pin = LeanArtifact.load(vm, referenceDir);
        vm.etch(target, pin.code);
        return target;
    }

    /// @notice Measures one frame, requiring it to return successfully.
    function _gas(address target, bytes memory input)
        internal
        view
        returns (uint256 gasUsed, bytes memory ret)
    {
        GasProbe.Result memory result = GasProbe.probe(target, input);
        require(result.ok, "GasCrossCheck: call reverted");
        return (result.gasUsed, result.ret);
    }

    /// @notice Checks the property each `Scorer.lean` checks by scoring every
    ///         vector twice, from a clean and a dirty initial state: the frame's
    ///         gas must not depend on the account's storage or balance.
    /// @dev The scorers' dirty state also sets transient storage and a nonzero
    ///      call value. Transient storage cannot be seeded from a cheatcode, and
    ///      a value-bearing call cannot be a `STATICCALL`; the storage and
    ///      balance half is checked here, and the scorers report clean and dirty
    ///      agreeing on every vector.
    function _assertGasIsStateIndependent(address target, bytes memory input, string memory label) internal {
        (uint256 clean,) = _gas(target, input);

        vm.store(target, bytes32(0), bytes32(uint256(0xdeadbeef)));
        vm.deal(target, 1 ether);

        (uint256 dirty,) = _gas(target, input);
        assertEq(dirty, clean, label);
    }

    // ── report formatting ───────────────────────────────────────────

    function _header(string memory title) internal pure {
        console2.log("");
        console2.log(title);
        console2.log(
            string.concat(
                _rpad("vector", 30),
                _rpad("bytes", 7),
                _rpad("lean gas", 12),
                _rpad("forge gas", 12),
                "  delta"
            )
        );
    }

    function _row(string memory label, uint256 size, uint256 leanGas, uint256 forgeGas) internal pure {
        console2.log(
            string.concat(
                _rpad(label, 30),
                _rpad(vm.toString(size), 7),
                _rpad(vm.toString(leanGas), 12),
                _rpad(vm.toString(forgeGas), 12),
                "  ",
                _delta(leanGas, forgeGas)
            )
        );
    }

    function _delta(uint256 leanGas, uint256 forgeGas) internal pure returns (string memory) {
        if (forgeGas == leanGas) return "0";
        if (forgeGas > leanGas) return string.concat("+", vm.toString(forgeGas - leanGas));
        return string.concat("-", vm.toString(leanGas - forgeGas));
    }

    /// @notice Renders `num / den` with two decimals, rounded half-up so the
    ///         result is directly comparable with the README gas tables.
    function _ratio(uint256 num, uint256 den) internal pure returns (string memory) {
        if (den == 0) return "n/a";
        uint256 scaled = (num * 100 + den / 2) / den;
        return string.concat(vm.toString(scaled / 100), ".", _twoDigits(scaled % 100), "x");
    }

    function _twoDigits(uint256 v) private pure returns (string memory) {
        return v < 10 ? string.concat("0", vm.toString(v)) : vm.toString(v);
    }

    /// @dev Left-aligns `s` in a `width`-character column.
    function _rpad(string memory s, uint256 width) internal pure returns (string memory out) {
        out = s;
        uint256 len = bytes(s).length;
        while (len < width) {
            out = string.concat(out, " ");
            len++;
        }
    }
}
