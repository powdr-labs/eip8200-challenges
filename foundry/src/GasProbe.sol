// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

/// @title GasProbe
/// @notice Measures the gas a callee frame consumes, which is the quantity the
///         Lean scorers report.
///
/// @dev Every `Scorer.lean` reports `start.gasAvailable - final.gasAvailable`
///      for a frame that runs the candidate `code` with the vector as
///      calldata. That is the frame's total consumption, including its own
///      memory expansion, and it excludes everything outside the frame: no
///      intrinsic transaction cost, no calldata byte cost, and no charge for
///      the call instruction that enters the frame.
///
///      Reading `gas()` around a `STATICCALL` measures more than that: the
///      call instruction's own account-access charge plus the surrounding
///      stack traffic. This probe removes that overhead exactly rather than
///      estimating it.
///
///      1. The measured call and the calibration call are the same
///         `STATICCALL` instruction, executed twice by a two-iteration loop
///         with only the target register differing. Sharing one call site is
///         what makes the overhead identical: at two separate call sites the
///         compiler is free to set up the stack differently — a constant
///         target costs a `PUSH20` where a variable one may already be in
///         place — and such a difference lands directly in the result.
///      2. Both targets are warmed with `EXTCODESIZE` before the loop, so each
///         `STATICCALL` is the warm 100-gas case regardless of what earlier
///         calls touched (EIP-2929). The warming result is compared against a
///         value `EXTCODESIZE` cannot return, because an unused `EXTCODESIZE`
///         is dead code that the optimizer removes.
///      3. The argument buffer is reserved from the free-memory pointer and
///         its last word is written before the snapshot, so neither call pays
///         caller-side memory expansion.
///      4. The calibration target holds a single `STOP`: a frame that consumes
///         exactly zero gas. Whatever iteration 0 reports is overhead and
///         nothing else.
///
///      Subtracting (4) from (1) leaves the frame's own consumption. The
///      residual is checked, not assumed: `GasProbeTest` measures the
///      `0x02`/`0x03` precompiles through this same probe and asserts the
///      results equal their exact published schedules.
library GasProbe {
    /// @dev Calibration target, holding runtime code `0x00` (`STOP`).
    ///      `GasCrossCheck.setUp` etches it.
    address internal constant STOP_TARGET = address(uint160(0x570b));

    struct Result {
        bool ok;
        uint256 gasUsed;
        bytes ret;
    }

    /// @notice Runs `target` with `input` as calldata and reports the frame's
    ///         exact gas consumption together with its returndata.
    /// @param target Address holding the runtime code under measurement.
    /// @param input Calldata for the frame, byte for byte as the Lean scorer
    ///        supplies it.
    function probe(address target, bytes memory input) internal view returns (Result memory result) {
        return _probe(target, input, 0);
    }

    /// @notice `probe` with an explicit gas cap for each callee frame.
    /// @dev The cap prevents a non-halting or exceptionally halting target from
    ///      consuming an arbitrarily large surrounding test budget. It does not
    ///      change the reported gas when the target halts below `gasLimit`.
    function probeCapped(address target, bytes memory input, uint256 gasLimit)
        internal
        view
        returns (Result memory result)
    {
        require(gasLimit != 0, "GasProbe: zero gas limit");
        require(
            gasleft() > 100_000 && gasLimit < (gasleft() - 100_000) / 2, "GasProbe: insufficient gas for cap"
        );
        return _probe(target, input, gasLimit);
    }

    /// @dev A zero `gasLimit` forwards the ordinary `gas()` amount. Otherwise
    ///      both iterations use the same explicit cap at the same call site.
    function _probe(address target, bytes memory input, uint256 gasLimit)
        private
        view
        returns (Result memory result)
    {
        uint256 argOffset = _reserveArgBuffer(input);
        uint256 argLen = input.length;
        address calibrationTarget = STOP_TARGET;

        uint256 overhead;
        uint256 measured;
        bool ok;
        bytes memory ret;
        assembly {
            // Warm both targets outside the measured window. The comparison
            // against `not(0)` — a size no account can have — keeps the access
            // observable so the optimizer cannot discard it.
            if eq(extcodesize(calibrationTarget), not(0)) { revert(0, 0) }
            if eq(extcodesize(target), not(0)) { revert(0, 0) }

            // Iteration 0 calibrates against the zero-gas frame; iteration 1
            // measures. One call site, so one instruction sequence.
            let current := calibrationTarget
            for { let i := 0 } lt(i, 2) { i := add(i, 1) } {
                if i { current := target }

                let forwarded := gas()
                if gasLimit { forwarded := gasLimit }
                let before := gas()
                let success := staticcall(forwarded, current, argOffset, argLen, 0, 0)
                let used := sub(before, gas())

                // Measurement closed; the rest is bookkeeping.
                switch i
                case 0 { overhead := used }
                default {
                    measured := used
                    ok := success
                    let size := returndatasize()
                    ret := mload(0x40)
                    mstore(0x40, add(ret, add(0x20, mul(div(add(size, 31), 32), 32))))
                    mstore(ret, size)
                    returndatacopy(add(ret, 0x20), 0, size)
                }
            }
        }

        require(measured >= overhead, "GasProbe: overhead exceeds measurement");

        result.ok = ok;
        result.gasUsed = measured - overhead;
        result.ret = ret;
    }

    /// @dev Copies `input` into a freshly reserved, word-aligned buffer and
    ///      expands memory past its end. Both calls then use this one offset,
    ///      so the call instruction's memory charge is zero for both.
    function _reserveArgBuffer(bytes memory input) private pure returns (uint256 argOffset) {
        assembly {
            let len := mload(input)
            argOffset := mload(0x40)
            // One spare word beyond the arguments keeps the pre-expanding
            // write inside this reservation even when `len` is zero.
            let end := add(argOffset, add(mul(div(add(len, 31), 32), 32), 0x20))
            mstore(0x40, end)

            for { let i := 0 } lt(i, len) { i := add(i, 0x20) } {
                mstore(add(argOffset, i), mload(add(add(input, 0x20), i)))
            }

            // Expand memory to `end` before any measurement begins.
            mstore(sub(end, 0x20), 0)
        }
    }
}
