import Challenge.EvmProof.Ops
import Challenge.EvmProof.Program
import YulEvmCompiler.Instr
set_option warningAsError true
/-!
# A reusable symbolic stepper for pure EVM bytecode

`runInstr` executes the opcode subset used by the reference SHA-256 artifact.
It deliberately has no cases for calls, storage, logs, or cryptographic
opcodes.  `runInstr_sound` proves each successful symbolic evaluation against
the relational EVM semantics.  A raw-bytecode proof therefore reduces its
straight-line blocks with this evaluator and supplies only decoder facts for
its own artifact.
-/

namespace Challenge.EvmProof.Stepper

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-- The decoder fact corresponding to an instruction-boundary certificate. -/
def Decodes (s : State) : Instr → Prop
  | .push width value =>
      s.decoded = some (.Push ⟨width⟩, some (value, width.val))
  | .op op => s.decodedOp = some op

private theorem stackCap (s : State) (op : Operation)
    (h : s.stack.length < 1024) :
    s.stack.length + Operation.pushArity op ≤
      1024 + Operation.popArity op := by
  have hop : Operation.pushArity op ≤ Operation.popArity op + 1 := by
    cases op with
    | StopArith op => cases op <;> decide
    | CompBit op => cases op <;> decide
    | Keccak op => cases op; decide
    | Env op => cases op <;> decide
    | Block op => cases op <;> decide
    | StackMemFlow op => cases op <;> decide
    | Push op => simp [Operation.pushArity, Operation.popArity]
    | Dup op => simp [Operation.pushArity, Operation.popArity]
    | Swap op => simp [Operation.pushArity, Operation.popArity]
    | DupN op => simp [Operation.pushArity, Operation.popArity]
    | SwapN op => simp [Operation.pushArity, Operation.popArity]
    | Exchange op => simp [Operation.pushArity, Operation.popArity]
    | Log op => simp [Operation.pushArity, Operation.popArity]
    | System op => cases op <;> decide
  omega

/-- Execute one supported instruction, omitting gas from the output state.
The uniform stack bound is slightly stronger than the opcode-specific EVM
side conditions and makes successful results immediately safe to lift. -/
def runInstr (instruction : Instr) (s : State) : Option State :=
  if s.stack.length < 1024 then
    match instruction with
    | .push width value =>
        if width.val = 0 then
          some { s with stack := ⟨0⟩ :: s.stack, pc := s.pc.succ }
        else
          some { s with
            stack := value :: s.stack
            pc := s.pc + UInt256.ofNat (width.val + 1) }
    | .op .ADD => match s.stack with
        | a :: b :: rest => some { s with stack := (a + b) :: rest, pc := s.pc.succ }
        | _ => none
    | .op .MUL => match s.stack with
        | a :: b :: rest => some { s with stack := (a * b) :: rest, pc := s.pc.succ }
        | _ => none
    | .op .SUB => match s.stack with
        | a :: b :: rest => some { s with stack := (a - b) :: rest, pc := s.pc.succ }
        | _ => none
    | .op .DIV => match s.stack with
        | a :: b :: rest => some { s with stack := (a / b) :: rest, pc := s.pc.succ }
        | _ => none
    | .op .MOD => match s.stack with
        | a :: b :: rest => some { s with stack := (a % b) :: rest, pc := s.pc.succ }
        | _ => none
    | .op .ADDMOD => match s.stack with
        | a :: b :: n :: rest => some { s with
            stack := UInt256.addMod a b n :: rest, pc := s.pc.succ }
        | _ => none
    | .op .MULMOD => match s.stack with
        | a :: b :: n :: rest => some { s with
            stack := UInt256.mulMod a b n :: rest, pc := s.pc.succ }
        | _ => none
    | .op .LT => match s.stack with
        | a :: b :: rest => some { s with stack := UInt256.lt a b :: rest, pc := s.pc.succ }
        | _ => none
    | .op .GT => match s.stack with
        | a :: b :: rest => some { s with stack := UInt256.gt a b :: rest, pc := s.pc.succ }
        | _ => none
    | .op .EQ => match s.stack with
        | a :: b :: rest => some { s with stack := UInt256.eq a b :: rest, pc := s.pc.succ }
        | _ => none
    | .op .BYTE => match s.stack with
        | i :: x :: rest => some { s with
            stack := UInt256.byteAt i x :: rest, pc := s.pc.succ }
        | _ => none
    | .op .ISZERO => match s.stack with
        | a :: rest => some { s with stack := UInt256.isZero a :: rest, pc := s.pc.succ }
        | _ => none
    | .op .AND => match s.stack with
        | a :: b :: rest => some { s with stack := UInt256.land a b :: rest, pc := s.pc.succ }
        | _ => none
    | .op .OR => match s.stack with
        | a :: b :: rest => some { s with stack := UInt256.lor a b :: rest, pc := s.pc.succ }
        | _ => none
    | .op .XOR => match s.stack with
        | a :: b :: rest => some { s with stack := UInt256.xor a b :: rest, pc := s.pc.succ }
        | _ => none
    | .op .NOT => match s.stack with
        | a :: rest => some { s with stack := UInt256.lnot a :: rest, pc := s.pc.succ }
        | _ => none
    | .op .SHL => match s.stack with
        | shift :: value :: rest => some { s with
            stack := UInt256.shiftLeft value shift :: rest, pc := s.pc.succ }
        | _ => none
    | .op .SHR => match s.stack with
        | shift :: value :: rest => some { s with
            stack := UInt256.shiftRight value shift :: rest, pc := s.pc.succ }
        | _ => none
    | .op .POP => match s.stack with
        | _ :: rest => some { s with stack := rest, pc := s.pc.succ }
        | _ => none
    | .op (.Dup n) => match s.stack[n.idx.val]? with
        | some value => some { s with stack := value :: s.stack, pc := s.pc.succ }
        | none => none
    | .op (.Swap n) => match s.stack.exchange 0 (n.idx.val + 1) with
        | some stack => some { s with stack := stack, pc := s.pc.succ }
        | none => none
    | .op .CALLDATASIZE => some { s with
        stack := UInt256.ofNat s.executionEnv.calldata.size :: s.stack
        pc := s.pc.succ }
    | .op .CALLDATALOAD => match s.stack with
        | offset :: rest => some { s with
            stack := MachineState.readWord s.executionEnv.calldata offset.toNat :: rest
            pc := s.pc.succ }
        | _ => none
    | .op .CALLDATACOPY => match s.stack with
        | destOff :: srcOff :: size :: rest => some { s with
            stack := rest
            pc := s.pc.succ
            activeWords := s.activeWordsAfterUInt256 destOff.toNat size.toNat
            memory := MachineState.writeBytes s.memory
              (MachineState.readPadded s.executionEnv.calldata
                srcOff.toNat size.toNat) destOff.toNat }
        | _ => none
    | .op .MLOAD => match s.stack with
        | offset :: rest => some { s with
            stack := MachineState.readWord s.memory offset.toNat :: rest
            pc := s.pc.succ
            activeWords := s.activeWordsAfterUInt256 offset.toNat 32 }
        | _ => none
    | .op .MSTORE => match s.stack with
        | offset :: value :: rest => some { s with
            stack := rest
            pc := s.pc.succ
            memory := MachineState.writeBytes s.memory
              (Data.Bytes.natToBytesPadded value.toNat 32) offset.toNat
            activeWords := s.activeWordsAfterUInt256 offset.toNat 32 }
        | _ => none
    | .op .MSTORE8 => match s.stack with
        | offset :: value :: rest => some { s with
            stack := rest
            pc := s.pc.succ
            memory := MachineState.writeBytes s.memory
              (ByteArray.mk #[UInt8.ofNat (value.toNat % 256)]) offset.toNat
            activeWords := s.activeWordsAfterUInt256 offset.toNat 1 }
        | _ => none
    | .op .MCOPY => match s.stack with
        | destOff :: srcOff :: size :: rest => some { s with
            stack := rest
            pc := s.pc.succ
            memory := MachineState.writeBytes s.memory
              (MachineState.readPadded s.memory srcOff.toNat size.toNat)
              destOff.toNat
            activeWords := s.activeWordsAfterUInt256_2
              destOff.toNat size.toNat srcOff.toNat size.toNat }
        | _ => none
    | .op .JUMP => match s.stack with
        | dest :: rest =>
            if Decode.isValidJumpDest s.executionEnv.code dest.toNat then
              some { s with stack := rest, pc := dest }
            else none
        | _ => none
    | .op .JUMPI => match s.stack with
        | dest :: condition :: rest =>
            if UInt256.isTrue condition then
              if Decode.isValidJumpDest s.executionEnv.code dest.toNat then
                some { s with stack := rest, pc := dest }
              else none
            else some { s with stack := rest, pc := s.pc.succ }
        | _ => none
    | .op .JUMPDEST => some { s with pc := s.pc.succ }
    | .op .RETURN => match s.stack with
        | offset :: size :: rest => some { s with
            halt := .Returned
            hReturn := MachineState.readPadded s.memory offset.toNat size.toNat
            stack := rest
            activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat }
        | _ => none
    | _ => none
  else none

/-- Exact gas charged by a successful `runInstr` step.  Keeping this
projection separate from `runInstr_sound` makes gas metering executable: Lean
does not need to normalize the semantic trace proof to read its cost. -/
def instrCost : Instr → State → Nat
  | .push width _, s => Gas.baseCost s.fork (.Push ⟨width⟩)
  | .op .CALLDATACOPY, s => Gas.totalCost s .CALLDATACOPY
  | .op .MLOAD, s => Gas.totalCost s .MLOAD
  | .op .MSTORE, s => Gas.totalCost s .MSTORE
  | .op .MSTORE8, s => Gas.totalCost s .MSTORE8
  | .op .MCOPY, s => Gas.totalCost s .MCOPY
  | .op .RETURN, s => Gas.totalCost s .RETURN
  | .op op, s => Gas.baseCost s.fork op

syntax "makeBinarySound " ident " for " term " via " term : command

macro_rules
  | `(makeBinarySound $name:ident for $op:term via $rule:term) =>
    `(private def $name {s t : State}
        (hdecode : s.decodedOp = some $op)
        (hresult : runInstr (.op $op) s = some t)
        (hrun : s.halt = .Running)
        (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
          s.executionEnv.codeAddr = false) : GasSteps s t := by
      refine ⟨Gas.baseCost s.fork $op, ?_⟩
      intro gas hgas
      by_cases hcap : s.stack.length < 1024
      · rw [runInstr, if_pos hcap] at hresult
        cases hs : s.stack with
        | nil => simp [hs] at hresult
        | cons a tail =>
          cases ht : tail with
          | nil => simp [hs, ht] at hresult
          | cons b rest =>
            have hstack : s.stack = a :: b :: rest := by simp [hs, ht]
            simp [hs, ht] at hresult
            subst t
            exact (($rule hdecode hstack (stackCap s $op hcap) hrun hnp).trace
              gas hgas)
      · simp [runInstr, hcap] at hresult)

syntax "makeUnarySound " ident " for " term " via " term : command

macro_rules
  | `(makeUnarySound $name:ident for $op:term via $rule:term) =>
    `(private def $name {s t : State}
        (hdecode : s.decodedOp = some $op)
        (hresult : runInstr (.op $op) s = some t)
        (hrun : s.halt = .Running)
        (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
          s.executionEnv.codeAddr = false) : GasSteps s t := by
      refine ⟨Gas.baseCost s.fork $op, ?_⟩
      intro gas hgas
      by_cases hcap : s.stack.length < 1024
      · rw [runInstr, if_pos hcap] at hresult
        cases hs : s.stack with
        | nil => simp [hs] at hresult
        | cons a rest =>
          simp [hs] at hresult
          subst t
          exact (($rule hdecode hs (stackCap s $op hcap) hrun hnp).trace
            gas hgas)
      · simp [runInstr, hcap] at hresult)

makeBinarySound sound_add for .ADD via GasStep.add
makeBinarySound sound_mul for .MUL via GasStep.mul
makeBinarySound sound_sub for .SUB via GasStep.sub
makeBinarySound sound_div for .DIV via GasStep.div
makeBinarySound sound_mod for .MOD via GasStep.mod
makeBinarySound sound_lt for .LT via GasStep.lt
makeBinarySound sound_gt for .GT via GasStep.gt
makeBinarySound sound_eq for .EQ via GasStep.eq
makeBinarySound sound_byte for .BYTE via GasStep.byte
makeBinarySound sound_and for .AND via GasStep.land
makeBinarySound sound_or for .OR via GasStep.lor
makeBinarySound sound_xor for .XOR via GasStep.xor
makeBinarySound sound_shl for .SHL via GasStep.shl
makeBinarySound sound_shr for .SHR via GasStep.shr
makeUnarySound sound_iszero for .ISZERO via GasStep.iszero
makeUnarySound sound_not for .NOT via GasStep.lnot
makeUnarySound sound_pop for .POP via GasStep.pop

syntax "makeTernarySound " ident " for " term " via " term : command

macro_rules
  | `(makeTernarySound $name:ident for $op:term via $rule:term) =>
    `(private def $name {s t : State}
        (hdecode : s.decodedOp = some $op)
        (hresult : runInstr (.op $op) s = some t)
        (hrun : s.halt = .Running)
        (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
          s.executionEnv.codeAddr = false) : GasSteps s t := by
      refine ⟨Gas.baseCost s.fork $op, ?_⟩
      intro gas hgas
      by_cases hcap : s.stack.length < 1024
      · rw [runInstr, if_pos hcap] at hresult
        cases hs : s.stack with
        | nil => simp [hs] at hresult
        | cons a tail =>
          cases ht : tail with
          | nil => simp [hs, ht] at hresult
          | cons b tail' =>
            cases hu : tail' with
            | nil => simp [hs, ht, hu] at hresult
            | cons n rest =>
              have hstack : s.stack = a :: b :: n :: rest := by simp [hs, ht, hu]
              simp [hs, ht, hu] at hresult
              subst t
              exact (($rule hdecode hstack (stackCap s $op hcap) hrun hnp).trace
                gas hgas)
      · simp [runInstr, hcap] at hresult)

makeTernarySound sound_addmod for .ADDMOD via GasStep.addmod
makeTernarySound sound_mulmod for .MULMOD via GasStep.mulmod

private def sound_push {s t : State} (width : Fin 33) (value : UInt256)
    (hdecode : Decodes s (.push width value))
    (hresult : runInstr (.push width value) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.push width value) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    by_cases hzero : width.val = 0
    · rw [if_pos hzero] at hresult
      have hwidth : width = ⟨0, by decide⟩ := Fin.ext hzero
      subst width
      simp at hresult
      subst t
      exact (GasStep.push0 (State.decoded_to_op hdecode) hcap hrun hnp).trace
        gas hgas
    · rw [if_neg hzero] at hresult
      simp at hresult
      subst t
      exact (GasStep.pushN width value width.val (Nat.pos_of_ne_zero hzero)
        hdecode hcap hrun hnp).trace gas hgas
  · simp [runInstr, hcap] at hresult

private def sound_dup {s t : State} (n : Operation.DupOp)
    (hdecode : s.decodedOp = some (.Dup n))
    (hresult : runInstr (.op (.Dup n)) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op (.Dup n)) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    cases hget : s.stack[n.idx.val]? with
    | some value =>
      rw [hget] at hresult
      injection hresult
      subst t
      exact (GasStep.dup n.idx value hdecode hget hcap hrun hnp).trace gas hgas
    | none => simp [hget] at hresult
  · simp [runInstr, hcap] at hresult

private def sound_swap {s t : State} (n : Operation.SwapOp)
    (hdecode : s.decodedOp = some (.Swap n))
    (hresult : runInstr (.op (.Swap n)) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op (.Swap n)) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    cases hswap : s.stack.exchange 0 (n.idx.val + 1) with
    | some stack =>
      rw [hswap] at hresult
      injection hresult
      subst t
      exact (GasStep.swap n.idx stack hdecode hswap
        (stackCap s (.Swap n) hcap) hrun hnp).trace gas hgas
    | none => simp [hswap] at hresult
  · simp [runInstr, hcap] at hresult

private def sound_calldatasize {s t : State}
    (hdecode : s.decodedOp = some .CALLDATASIZE)
    (hresult : runInstr (.op .CALLDATASIZE) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .CALLDATASIZE) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    simp at hresult
    subst t
    exact (GasStep.calldatasize hdecode hcap hrun hnp).trace gas hgas
  · simp [runInstr, hcap] at hresult

private def sound_calldataload {s t : State}
    (hdecode : s.decodedOp = some .CALLDATALOAD)
    (hresult : runInstr (.op .CALLDATALOAD) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .CALLDATALOAD) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    cases hstack : s.stack with
    | nil => simp [hstack] at hresult
    | cons offset rest =>
      simp [hstack] at hresult
      subst t
      exact (GasStep.calldataload offset rest hdecode hstack
        (stackCap s .CALLDATALOAD hcap) hrun hnp).trace gas hgas
  · simp [runInstr, hcap] at hresult

private def sound_calldatacopy {s t : State}
    (hdecode : s.decodedOp = some .CALLDATACOPY)
    (hresult : runInstr (.op .CALLDATACOPY) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .CALLDATACOPY) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    match hstack : s.stack with
    | destOff :: srcOff :: size :: rest =>
      simp [hstack] at hresult
      subst t
      let g := GasStep.calldatacopy destOff srcOff size rest hdecode hstack
        (stackCap s .CALLDATACOPY hcap) hrun hnp
      have hg : g.cost ≤ gas := by
        simpa [g, GasStep.calldatacopy, GasStep.of_running, GasSteps.one,
          instrCost, Gas.totalCost, hstack] using hgas
      simpa [g, GasStep.calldatacopy, GasStep.of_running, GasSteps.one,
        instrCost, Gas.totalCost, hstack] using g.trace gas hg
    | [] => simp [hstack] at hresult
    | _ :: [] => simp [hstack] at hresult
    | _ :: _ :: [] => simp [hstack] at hresult
  · simp [runInstr, hcap] at hresult

private def sound_mload {s t : State}
    (hdecode : s.decodedOp = some .MLOAD)
    (hresult : runInstr (.op .MLOAD) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .MLOAD) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    cases hstack : s.stack with
    | nil => simp [hstack] at hresult
    | cons offset rest =>
      simp [hstack] at hresult
      subst t
      let g := GasStep.mload offset rest hdecode hstack
        (stackCap s .MLOAD hcap) hrun hnp
      have hg : g.cost ≤ gas := by
        simpa [g, GasStep.mload, GasStep.of_running, GasSteps.one,
          instrCost, Gas.totalCost, hstack] using hgas
      simpa [g, GasStep.mload, GasStep.of_running, GasSteps.one,
        instrCost, Gas.totalCost, hstack] using g.trace gas hg
  · simp [runInstr, hcap] at hresult

syntax "makeMemoryBinarySound " ident " for " term " via " term : command

macro_rules
  | `(makeMemoryBinarySound $name:ident for $op:term via $rule:term) =>
    `(private def $name {s t : State}
        (hdecode : s.decodedOp = some $op)
        (hresult : runInstr (.op $op) s = some t)
        (hrun : s.halt = .Running)
        (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
          s.executionEnv.codeAddr = false) : GasSteps s t := by
      refine ⟨Gas.totalCost s $op, ?_⟩
      intro gas hgas
      by_cases hcap : s.stack.length < 1024
      · rw [runInstr, if_pos hcap] at hresult
        cases hs : s.stack with
        | nil => simp [hs] at hresult
        | cons first tail =>
          cases ht : tail with
          | nil => simp [hs, ht] at hresult
          | cons second rest =>
            have hstack : s.stack = first :: second :: rest := by
              simp [hs, ht]
            simp [hs, ht] at hresult
            subst t
            let g := $rule first second rest hdecode hstack
              (stackCap s $op hcap) hrun hnp
            have hg : g.cost ≤ gas := by
              simpa [g, GasStep.of_running, GasSteps.one,
                Gas.totalCost, hstack] using hgas
            simpa [g, GasStep.of_running, GasSteps.one,
              Gas.totalCost, hstack] using g.trace gas hg
      · simp [runInstr, hcap] at hresult)

makeMemoryBinarySound sound_mstore for .MSTORE via GasStep.mstore
makeMemoryBinarySound sound_mstore8 for .MSTORE8 via GasStep.mstore8
makeMemoryBinarySound sound_return for .RETURN via GasStep.return_

private def sound_mcopy {s t : State}
    (hdecode : s.decodedOp = some .MCOPY)
    (hresult : runInstr (.op .MCOPY) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .MCOPY) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    match hstack : s.stack with
    | destOff :: srcOff :: size :: rest =>
      simp [hstack] at hresult
      subst t
      let g := GasStep.mcopy destOff srcOff size rest hdecode hstack
        (stackCap s .MCOPY hcap) hrun hnp
      have hg : g.cost ≤ gas := by
        simpa [g, GasStep.mcopy, GasStep.of_running, GasSteps.one,
          instrCost, Gas.totalCost, hstack] using hgas
      simpa [g, GasStep.mcopy, GasStep.of_running, GasSteps.one,
        instrCost, Gas.totalCost, hstack] using g.trace gas hg
    | [] => simp [hstack] at hresult
    | _ :: [] => simp [hstack] at hresult
    | _ :: _ :: [] => simp [hstack] at hresult
  · simp [runInstr, hcap] at hresult

private def sound_jump {s t : State}
    (hdecode : s.decodedOp = some .JUMP)
    (hresult : runInstr (.op .JUMP) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .JUMP) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    cases hstack : s.stack with
    | nil => simp [hstack] at hresult
    | cons dest rest =>
      by_cases hvalid : Decode.isValidJumpDest
          s.executionEnv.code dest.toNat = true
      · simp [hstack, hvalid] at hresult
        subst t
        exact (GasStep.jump dest rest hdecode hstack hvalid
          (stackCap s .JUMP hcap) hrun hnp).trace gas hgas
      · simp [hstack, hvalid] at hresult
  · simp [runInstr, hcap] at hresult

private def sound_jumpi {s t : State}
    (hdecode : s.decodedOp = some .JUMPI)
    (hresult : runInstr (.op .JUMPI) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .JUMPI) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons dest tail =>
      cases ht : tail with
      | nil => simp [hs, ht] at hresult
      | cons condition rest =>
        have hstack : s.stack = dest :: condition :: rest := by simp [hs, ht]
        by_cases hcondition : UInt256.isTrue condition
        · by_cases hvalid : Decode.isValidJumpDest
              s.executionEnv.code dest.toNat = true
          · simp [hs, ht, hcondition, hvalid] at hresult
            subst t
            exact (GasStep.jumpiTaken dest condition rest hdecode hstack
              hcondition hvalid (stackCap s .JUMPI hcap) hrun hnp).trace
              gas hgas
          · simp [hs, ht, hcondition, hvalid] at hresult
        · simp [hs, ht, hcondition] at hresult
          subst t
          exact (GasStep.jumpiNotTaken dest condition rest hdecode hstack
            hcondition (stackCap s .JUMPI hcap) hrun hnp).trace gas hgas
  · simp [runInstr, hcap] at hresult

private def sound_jumpdest {s t : State}
    (hdecode : s.decodedOp = some .JUMPDEST)
    (hresult : runInstr (.op .JUMPDEST) s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost (.op .JUMPDEST) s, ?_⟩
  intro gas hgas
  by_cases hcap : s.stack.length < 1024
  · rw [runInstr, if_pos hcap] at hresult
    simp at hresult
    subst t
    exact (GasStep.jumpdest hdecode (stackCap s .JUMPDEST hcap) hrun hnp).trace
      gas hgas
  · simp [runInstr, hcap] at hresult

/-- Every successful evaluator result is a gas-parametric trace in the
relational EVM semantics. This is the only definition block proofs need to use. -/
def runInstr_sound {instruction : Instr} {s t : State}
    (hdecode : Decodes s instruction)
    (hresult : runInstr instruction s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost instruction s, ?_⟩
  intro gas hgas
  cases instruction with
  | push width value =>
      exact (sound_push width value hdecode hresult hrun hnp).trace gas hgas
  | op op =>
    change s.decodedOp = some op at hdecode
    cases op with
    | StopArith op =>
      cases op <;> first
        | exact (sound_add hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_mul hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_sub hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_div hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_mod hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_addmod hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_mulmod hdecode hresult hrun hnp).trace gas hgas
        | simp [runInstr] at hresult
    | CompBit op =>
      cases op <;> first
        | exact (sound_lt hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_gt hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_eq hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_byte hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_iszero hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_and hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_or hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_xor hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_not hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_shl hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_shr hdecode hresult hrun hnp).trace gas hgas
        | simp [runInstr] at hresult
    | Env op =>
      cases op <;> first
        | exact (sound_calldataload hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_calldatasize hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_calldatacopy hdecode hresult hrun hnp).trace gas hgas
        | simp [runInstr] at hresult
    | StackMemFlow op =>
      cases op <;> first
        | exact (sound_pop hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_mload hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_mstore hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_mstore8 hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_jump hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_jumpi hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_jumpdest hdecode hresult hrun hnp).trace gas hgas
        | exact (sound_mcopy hdecode hresult hrun hnp).trace gas hgas
        | simp [runInstr] at hresult
    | Dup n => exact (sound_dup n hdecode hresult hrun hnp).trace gas hgas
    | Swap n => exact (sound_swap n hdecode hresult hrun hnp).trace gas hgas
    | System op =>
      cases op <;> first
        | exact (sound_return hdecode hresult hrun hnp).trace gas hgas
        | simp [runInstr] at hresult
    | Keccak op => cases op; simp [runInstr] at hresult
    | Block op => cases op <;> simp [runInstr] at hresult
    | Push op => simp [runInstr] at hresult
    | DupN op => simp [runInstr] at hresult
    | SwapN op => simp [runInstr] at hresult
    | Exchange op => simp [runInstr] at hresult
    | Log op => simp [runInstr] at hresult

@[simp] theorem runInstr_sound_cost {instruction : Instr} {s t : State}
    (hdecode : Decodes s instruction)
    (hresult : runInstr instruction s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (runInstr_sound hdecode hresult hrun hnp).cost = instrCost instruction s :=
  rfl

/-- Structural and fork-specific conditions under which an artifact
instruction decodes exactly as its instruction-boundary view claims. -/
def WellFormed (fork : Fork) : Instr → Prop
  | .push width value =>
      value.toNat < 256 ^ width.val ∧
        (Operation.Push ⟨width⟩).availableInFork fork = true
  | .op op =>
      Decode.opcodeOf (Instr.opByte op) = some op ∧
        YulEvmCompiler.plainOp op ∧ op.availableInFork fork = true

instance (fork : Fork) (instruction : Instr) :
    Decidable (WellFormed fork instruction) := by
  cases instruction with
  | push width value => simp [WellFormed]; infer_instance
  | op op =>
    cases op <;> simp [WellFormed, YulEvmCompiler.plainOp] <;> infer_instance

theorem decodes_of_artifact (artifact : ProgramArtifact) (s : State)
    (index : Nat) (instruction : Instr)
    (hcode : s.executionEnv.code = artifact.code)
    (hpc : s.pc.toNat = artifact.instructionPC index)
    (hget : artifact.instructions[index]? = some instruction)
    (hwf : WellFormed s.fork instruction) : Decodes s instruction := by
  cases instruction with
  | push width value =>
    rcases hwf with ⟨hfit, havailable⟩
    exact artifact.state_decoded_of s index hcode hpc _ _
      (artifact.decodeAt_push_index index width value hget hfit) havailable
  | op op =>
    rcases hwf with ⟨hopcode, hplain, havailable⟩
    exact artifact.state_decodedOp_of s index hcode hpc op none
      (artifact.decodeAt_op_index index op hget hopcode hplain) havailable

/-- Evaluate the instruction at an artifact index, checking its PC and all
decoder side conditions.  The code equality remains an explicit theorem
premise because comparing a large byte array at every step would be wasteful. -/
def runAt (artifact : ProgramArtifact) (index : Nat) (s : State) : Option State := do
  if s.pc.toNat = artifact.instructionPC index then
    match artifact.instructions[index]? with
    | some instruction =>
        if WellFormed s.fork instruction then runInstr instruction s else none
    | none => none
  else none

def runAt_sound {artifact : ProgramArtifact} {index : Nat} {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hresult : runAt artifact index s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  unfold runAt at hresult
  split at hresult
  · rename_i hpc
    split at hresult
    · rename_i instruction hget
      split at hresult
      · rename_i hwf
        exact runInstr_sound
          (decodes_of_artifact artifact s index instruction hcode hpc hget hwf)
          hresult hrun hnp
      · simp_all
    · simp_all
  · simp_all

theorem runInstr_executionEnv {instruction : Instr} {s t : State}
    (hresult : runInstr instruction s = some t) :
    t.executionEnv = s.executionEnv := by
  unfold runInstr at hresult
  split at hresult
  · split at hresult
    all_goals
      repeat' first | split at hresult | simp_all
    all_goals subst t; rfl
  · simp_all

theorem runAt_executionEnv {artifact : ProgramArtifact} {index : Nat}
    {s t : State} (hresult : runAt artifact index s = some t) :
    t.executionEnv = s.executionEnv := by
  unfold runAt at hresult
  split at hresult
  · split at hresult
    · split at hresult
      · exact runInstr_executionEnv hresult
      · simp_all
    · simp_all
  · simp_all

/-- Evaluate a chosen control-flow path through an artifact.  Intermediate
states are required to remain running; the final instruction may be RETURN. -/
def runBlock (artifact : ProgramArtifact) : List Nat → State → Option State
  | [], s => some s
  | index :: rest, s =>
      match runAt artifact index s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runBlock artifact rest next
              | _ => none

def runBlock_sound (artifact : ProgramArtifact) (indices : List Nat)
    {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hresult : runBlock artifact indices s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  induction indices generalizing s t with
  | nil =>
      simp [runBlock] at hresult
      subst t
      exact GasSteps.refl s
  | cons index rest ih =>
      cases rest with
      | nil =>
          cases hnext : runAt artifact index s with
          | none => simp [runBlock, hnext] at hresult
          | some next =>
            simp [runBlock, hnext] at hresult
            subst t
            exact runAt_sound hcode hnext hrun hnp
      | cons nextIndex tail =>
          cases hnext : runAt artifact index s with
          | none => simp [runBlock, hnext] at hresult
          | some next =>
            cases hnextRun : next.halt with
            | Running =>
              simp [runBlock, hnext, hnextRun] at hresult
              have henv := runAt_executionEnv hnext
              have hnextCode : next.executionEnv.code = artifact.code := by
                rw [henv, hcode]
              have hnextNp : Precompile.isPrecompile next.executionEnv.fork
                  next.executionEnv.codeAddr = false := by
                simpa [henv] using hnp
              exact (runAt_sound hcode hnext hrun hnp).trans
                (ih hnextCode hresult hnextRun hnextNp)
            | Success => simp [runBlock, hnext, hnextRun] at hresult
            | Returned => simp [runBlock, hnext, hnextRun] at hresult
            | Reverted => simp [runBlock, hnext, hnextRun] at hresult
            | Exception error => simp [runBlock, hnext, hnextRun] at hresult

/-- A compact, proof-carrying instruction location.  Paths built from these
certificates never rescan the full instruction list during reduction. -/
structure Located (artifact : ProgramArtifact) (fork : Fork) where
  index : Nat
  instruction : Instr
  atIndex : artifact.instructions[index]? = some instruction
  wellFormed : WellFormed fork instruction

/-- One Boolean certificate establishes opcode availability and encoding
well-formedness for every instruction in an artifact. -/
def AllWellFormed (artifact : ProgramArtifact) (fork : Fork) : Prop :=
  artifact.instructions.all (fun instruction =>
    decide (WellFormed fork instruction)) = true

theorem AllWellFormed.valid {artifact : ProgramArtifact} {fork : Fork}
    (hcert : AllWellFormed artifact fork) {instruction : Instr}
    (hmem : instruction ∈ artifact.instructions) :
    WellFormed fork instruction := by
  exact of_decide_eq_true ((List.all_eq_true.mp hcert) instruction hmem)

/-- Build a proof-carrying location from an in-bounds instruction index and a
single whole-artifact well-formedness certificate. -/
def Located.ofIndex {artifact : ProgramArtifact} {fork : Fork}
    (hcert : AllWellFormed artifact fork)
    (index : Fin artifact.instructions.length) : Located artifact fork where
  index := index.val
  instruction := artifact.instructions[index.val]
  atIndex := List.getElem?_eq_getElem index.isLt
  wellFormed := hcert.valid (List.getElem_mem index.isLt)

def runLocated {artifact : ProgramArtifact} {fork : Fork}
    (located : Located artifact fork)
    (s : State) : Option State :=
  if s.pc.toNat = artifact.instructionPC located.index then
    runInstr located.instruction s
  else none

def runLocated_sound {artifact : ProgramArtifact}
    {fork : Fork} {located : Located artifact fork} {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runLocated located s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨instrCost located.instruction s, ?_⟩
  intro gas hgas
  unfold runLocated at hresult
  split at hresult
  · rename_i hpc
    have hwf : WellFormed s.fork located.instruction := by
      simpa [hfork] using located.wellFormed
    exact (runInstr_sound
      (decodes_of_artifact artifact s located.index located.instruction
        hcode hpc located.atIndex hwf) hresult hrun hnp
      ).trace gas hgas
  · simp_all

@[simp] theorem runLocated_sound_cost {artifact : ProgramArtifact}
    {fork : Fork} {located : Located artifact fork} {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runLocated located s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (runLocated_sound hcode hfork hresult hrun hnp).cost =
      instrCost located.instruction s := rfl

theorem runLocated_executionEnv {artifact : ProgramArtifact}
    {fork : Fork} {located : Located artifact fork} {s t : State}
    (hresult : runLocated located s = some t) :
    t.executionEnv = s.executionEnv := by
  unfold runLocated at hresult
  split at hresult
  · exact runInstr_executionEnv hresult
  · simp_all

def runLocatedBlock {artifact : ProgramArtifact} {fork : Fork} :
    List (Located artifact fork) → State → Option State
  | [], s => some s
  | located :: rest, s =>
      match runLocated located s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runLocatedBlock rest next
              | _ => none

/-- Executable exact cost of a located path.  On successful paths this follows
the same intermediate states as `runLocatedBlock`; failure branches are
irrelevant to `runLocatedBlock_sound` and return the cost accumulated so far. -/
def runLocatedBlockCost {artifact : ProgramArtifact} {fork : Fork} :
    List (Located artifact fork) → State → Nat
  | [], _ => 0
  | located :: rest, s =>
      instrCost located.instruction s +
        match rest with
        | [] => 0
        | _ :: _ =>
            match runLocated located s with
            | some next =>
                match next.halt with
                | .Running => runLocatedBlockCost rest next
                | _ => 0
            | none => 0

def runLocatedBlock_sound (artifact : ProgramArtifact)
    (fork : Fork) (path : List (Located artifact fork)) {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  refine ⟨runLocatedBlockCost path s, ?_⟩
  intro gas hgas
  induction path generalizing s t gas with
  | nil =>
      simp [runLocatedBlock] at hresult
      subst t
      simpa [runLocatedBlockCost, withGas] using
        Steps.refl (withGas s gas)
  | cons located rest ih =>
      cases rest with
      | nil =>
          cases hnext : runLocated located s with
          | none => simp [runLocatedBlock, hnext] at hresult
          | some next =>
            simp [runLocatedBlock, hnext] at hresult
            subst t
            exact (runLocated_sound hcode hfork hnext hrun hnp).trace gas
              (by simpa [runLocatedBlockCost] using hgas)
      | cons nextLocated tail =>
          cases hnext : runLocated located s with
          | none => simp [runLocatedBlock, hnext] at hresult
          | some next =>
            cases hnextRun : next.halt with
            | Running =>
              simp [runLocatedBlock, hnext, hnextRun] at hresult
              have henv := runLocated_executionEnv hnext
              have hnextCode : next.executionEnv.code = artifact.code := by
                rw [henv, hcode]
              have hnextNp : Precompile.isPrecompile next.executionEnv.fork
                  next.executionEnv.codeAddr = false := by
                simpa [henv] using hnp
              have hnextFork : next.fork = fork := by
                change next.executionEnv.fork = fork
                rw [henv]
                exact hfork
              let head := runLocated_sound hcode hfork hnext hrun hnp
              have hcost :
                  runLocatedBlockCost (located :: nextLocated :: tail) s =
                    head.cost +
                      runLocatedBlockCost (nextLocated :: tail) next := by
                simp [runLocatedBlockCost, hnext, hnextRun, head]
              have hhead : head.cost ≤ gas := by
                rw [hcost] at hgas
                omega
              have htail : runLocatedBlockCost (nextLocated :: tail) next ≤
                  gas - head.cost := by
                rw [hcost] at hgas
                omega
              have hsHead := head.trace gas hhead
              have hsTail := ih hnextCode hnextFork hresult hnextRun hnextNp
                (gas := gas - head.cost) htail
              have hsub :
                  gas - head.cost -
                      runLocatedBlockCost (nextLocated :: tail) next =
                    gas - runLocatedBlockCost
                      (located :: nextLocated :: tail) s := by
                rw [hcost]
                omega
              simpa [hsub] using hsHead.append hsTail
            | Success => simp [runLocatedBlock, hnext, hnextRun] at hresult
            | Returned => simp [runLocatedBlock, hnext, hnextRun] at hresult
            | Reverted => simp [runLocatedBlock, hnext, hnextRun] at hresult
            | Exception error =>
              simp [runLocatedBlock, hnext, hnextRun] at hresult

@[simp] theorem runLocatedBlock_sound_cost (artifact : ProgramArtifact)
    (fork : Fork) (path : List (Located artifact fork)) {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (runLocatedBlock_sound artifact fork path hcode hfork hresult hrun hnp).cost =
      runLocatedBlockCost path s := rfl

end Challenge.EvmProof.Stepper
