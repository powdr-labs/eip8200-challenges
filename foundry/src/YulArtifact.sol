// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Vm} from "forge-std/Vm.sol";
import {LeanArtifact} from "./LeanArtifact.sol";

/// @title YulArtifact
/// @notice Loads bytecode generated from a proved Yul source for execution-only tests.
/// @dev Unlike LeanArtifact, this deliberately makes no bytecode-proof claim. CI separately
///      recompiles the Yul source and requires it to reproduce this exact hex file.
library YulArtifact {
    function load(Vm vm, string memory referenceDir) internal view returns (bytes memory) {
        return LeanArtifact.parseHex(vm.readFile(string.concat(referenceDir, "/reference.hex")));
    }
}
