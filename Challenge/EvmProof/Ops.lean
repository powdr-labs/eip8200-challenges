import Challenge.EvmProof.Gas
set_option warningAsError true
/-!
# Gas-parametric opcode transitions

Small wrappers around `EvmSemantics.EVM.StepRunning` erase gas bookkeeping
from symbolic states.  They are deliberately parameterized by decoder facts,
so a raw-bytecode proof supplies only a certificate for the bytes at its
current program counter.
-/

namespace Challenge.EvmProof.GasStep

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

/-- Lift one successful `StepRunning` rule into the gas-parametric trace
algebra.  This is the common endpoint used by every opcode-specific symbolic
rule, including submission-specific rules written outside this module. -/
def of_running {s t : State} (cost : Nat)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hstep : ∀ gas, cost ≤ gas →
      StepRunning (withGas s gas) (withGas t (gas - cost))) :
    GasSteps s t := by
  apply GasSteps.one cost
  intro gas hgas
  exact Step.running
    (by simpa [withGas] using hrun)
    (by simpa [withGas] using hnp)
    (hstep gas hgas)

/-- The explicit `INVALID` instruction halts exceptionally without charging
an opcode fee. Keeping it in the shared stepper lets interface specifications
cover precompile-style malformed-input failure paths. -/
def invalid {s : State}
    (hop : s.decodedOp = some .INVALID)
    (hcap : s.stack.length + Operation.pushArity .INVALID ≤
      1024 + Operation.popArity .INVALID)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with halt := .Exception .InvalidInstruction } := by
  apply of_running 0 hrun hnp
  intro gas _
  simpa [withGas] using StepRunning.invalidOpcode (withGas s gas) hop hcap

def add {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .ADD)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .ADD ≤
      1024 + Operation.popArity .ADD)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := (a + b) :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .ADD
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.add (withGas s gas) a b rest hop hgas hstack hcap

def mul {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .MUL)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .MUL ≤
      1024 + Operation.popArity .MUL)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := (a * b) :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .MUL
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.mul (withGas s gas) a b rest hop hgas hstack hcap

def sub {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .SUB)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .SUB ≤
      1024 + Operation.popArity .SUB)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := (a - b) :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .SUB
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.sub (withGas s gas) a b rest hop hgas hstack hcap

def div {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .DIV)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .DIV ≤
      1024 + Operation.popArity .DIV)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := (a / b) :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .DIV
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.div (withGas s gas) a b rest hop hgas hstack hcap

def mod {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .MOD)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .MOD ≤
      1024 + Operation.popArity .MOD)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := (a % b) :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .MOD
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.mod (withGas s gas) a b rest hop hgas hstack hcap

def addmod {s : State} {a b n : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .ADDMOD)
    (hstack : s.stack = a :: b :: n :: rest)
    (hcap : s.stack.length + Operation.pushArity .ADDMOD ≤
      1024 + Operation.popArity .ADDMOD)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.addMod a b n :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .ADDMOD
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.addmod (withGas s gas) a b n rest hop hgas hstack hcap

def mulmod {s : State} {a b n : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .MULMOD)
    (hstack : s.stack = a :: b :: n :: rest)
    (hcap : s.stack.length + Operation.pushArity .MULMOD ≤
      1024 + Operation.popArity .MULMOD)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.mulMod a b n :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .MULMOD
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.mulmod (withGas s gas) a b n rest hop hgas hstack hcap

def lt {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .LT)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .LT ≤
      1024 + Operation.popArity .LT)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.lt a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .LT
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.lt (withGas s gas) a b rest hop hgas hstack hcap

def gt {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .GT)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .GT ≤
      1024 + Operation.popArity .GT)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.gt a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .GT
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.gt (withGas s gas) a b rest hop hgas hstack hcap

def eq {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .EQ)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .EQ ≤
      1024 + Operation.popArity .EQ)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.eq a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .EQ
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.eq (withGas s gas) a b rest hop hgas hstack hcap

def byte {s : State} {i x : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .BYTE)
    (hstack : s.stack = i :: x :: rest)
    (hcap : s.stack.length + Operation.pushArity .BYTE ≤
      1024 + Operation.popArity .BYTE)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.byteAt i x :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .BYTE
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.byte_ (withGas s gas) i x rest hop hgas hstack hcap

def iszero {s : State} {a : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .ISZERO)
    (hstack : s.stack = a :: rest)
    (hcap : s.stack.length + Operation.pushArity .ISZERO ≤
      1024 + Operation.popArity .ISZERO)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.isZero a :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .ISZERO
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.iszero (withGas s gas) a rest hop hgas hstack hcap

def land {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .AND)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .AND ≤
      1024 + Operation.popArity .AND)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.land a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .AND
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.and (withGas s gas) a b rest hop hgas hstack hcap

def lor {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .OR)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .OR ≤
      1024 + Operation.popArity .OR)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.lor a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .OR
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.or (withGas s gas) a b rest hop hgas hstack hcap

def xor {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .XOR)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .XOR ≤
      1024 + Operation.popArity .XOR)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.xor a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .XOR
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.xor_ (withGas s gas) a b rest hop hgas hstack hcap

def lnot {s : State} {a : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .NOT)
    (hstack : s.stack = a :: rest)
    (hcap : s.stack.length + Operation.pushArity .NOT ≤
      1024 + Operation.popArity .NOT)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.lnot a :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .NOT
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.not (withGas s gas) a rest hop hgas hstack hcap

def shl {s : State} {shift value : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .SHL)
    (hstack : s.stack = shift :: value :: rest)
    (hcap : s.stack.length + Operation.pushArity .SHL ≤
      1024 + Operation.popArity .SHL)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.shiftLeft value shift :: rest
      pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .SHL
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.shl (withGas s gas) shift value rest hop hgas hstack hcap

def shr {s : State} {shift value : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .SHR)
    (hstack : s.stack = shift :: value :: rest)
    (hcap : s.stack.length + Operation.pushArity .SHR ≤
      1024 + Operation.popArity .SHR)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.shiftRight value shift :: rest
      pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .SHR
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.shr (withGas s gas) shift value rest hop hgas hstack hcap

def jumpdest {s : State}
    (hop : s.decodedOp = some .JUMPDEST)
    (hcap : s.stack.length + Operation.pushArity .JUMPDEST ≤
      1024 + Operation.popArity .JUMPDEST)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .JUMPDEST
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.jumpdest (withGas s gas) hop hgas hcap

def push0 {s : State}
    (hop : s.decodedOp = some (.Push ⟨0, by decide⟩))
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := ⟨0⟩ :: s.stack, pc := s.pc.succ } := by
  let op : Operation := .Push ⟨0, by decide⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.push0 (withGas s gas) hop hgas hcap

def pushN {s : State} (k : Fin 33) (data : UInt256) (immWidth : Nat)
    (hk : 0 < k.val)
    (hdecoded : s.decoded =
      some (.Push ⟨k, k.isLt⟩, some (data, immWidth)))
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := data :: s.stack
      pc := s.pc + UInt256.ofNat (immWidth + 1) } := by
  let op : Operation := .Push ⟨k, k.isLt⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.pushN (withGas s gas) k data immWidth hk hdecoded hgas hcap

def pop {s : State} {a : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .POP)
    (hstack : s.stack = a :: rest)
    (hcap : s.stack.length + Operation.pushArity .POP ≤
      1024 + Operation.popArity .POP)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .POP
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.pop (withGas s gas) a rest hop hgas hstack hcap

def dup {s : State} (n : Fin 16) (value : UInt256)
    (hop : s.decodedOp = some (.Dup ⟨n⟩))
    (hget : s.stack[n.val]? = some value)
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := value :: s.stack, pc := s.pc.succ } := by
  let op : Operation := .Dup ⟨n⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.dup (withGas s gas) n value hop hgas hget hcap

def swap {s : State} (n : Fin 16) (stack' : List UInt256)
    (hop : s.decodedOp = some (.Swap ⟨n⟩))
    (hswap : s.stack.exchange 0 (n.val + 1) = some stack')
    (hcap : s.stack.length + Operation.pushArity (.Swap ⟨n⟩) ≤
      1024 + Operation.popArity (.Swap ⟨n⟩))
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := stack', pc := s.pc.succ } := by
  let op : Operation := .Swap ⟨n⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.swap (withGas s gas) n stack' hop hgas hswap hcap

def calldatasize {s : State}
    (hop : s.decodedOp = some .CALLDATASIZE)
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.ofNat s.executionEnv.calldata.size :: s.stack,
      pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .CALLDATASIZE
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.calldatasize (withGas s gas) hop hgas hcap

def calldataload {s : State} (offset : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .CALLDATALOAD)
    (hstack : s.stack = offset :: rest)
    (hcap : s.stack.length + Operation.pushArity .CALLDATALOAD ≤
      1024 + Operation.popArity .CALLDATALOAD)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := MachineState.readWord s.executionEnv.calldata offset.toNat :: rest
      pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .CALLDATALOAD
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.calldataload (withGas s gas) offset rest hop hgas hstack hcap

def calldatacopy {s : State} (destOff srcOff size : UInt256)
    (rest : List UInt256)
    (hop : s.decodedOp = some .CALLDATACOPY)
    (hstack : s.stack = destOff :: srcOff :: size :: rest)
    (hcap : s.stack.length + Operation.pushArity .CALLDATACOPY ≤
      1024 + Operation.popArity .CALLDATACOPY)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := rest
      pc := s.pc.succ
      activeWords := s.activeWordsAfterUInt256 destOff.toNat size.toNat
      memory := MachineState.writeBytes s.memory
        (MachineState.readPadded s.executionEnv.calldata srcOff.toNat size.toNat)
        destOff.toNat } := by
  let cost := Gas.calldatacopyTotal s destOff size
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.calldatacopyTotal,
    State.activeWordsAfterUInt256] using
    StepRunning.calldatacopy (withGas s gas) destOff srcOff size rest
      hop hstack hgas hcap

def mstore {s : State} (offset value : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .MSTORE)
    (hstack : s.stack = offset :: value :: rest)
    (hcap : s.stack.length + Operation.pushArity .MSTORE ≤
      1024 + Operation.popArity .MSTORE)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := rest
      pc := s.pc.succ
      memory := MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded value.toNat 32) offset.toNat
      activeWords := s.activeWordsAfterUInt256 offset.toNat 32 } := by
  let cost := Gas.mstoreTotal s offset
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.mstoreTotal, State.activeWordsAfterUInt256] using
    StepRunning.mstore (withGas s gas) offset value rest hop hstack hgas hcap

@[simp] theorem mstore_cost {s : State} (offset value : UInt256)
    (rest : List UInt256) (hop : s.decodedOp = some .MSTORE)
    (hstack : s.stack = offset :: value :: rest) (hcap) (hrun) (hnp) :
    (mstore (s := s) offset value rest hop hstack hcap hrun hnp).cost =
      Gas.mstoreTotal s offset := rfl

def mload {s : State} (offset : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .MLOAD)
    (hstack : s.stack = offset :: rest)
    (hcap : s.stack.length + Operation.pushArity .MLOAD ≤
      1024 + Operation.popArity .MLOAD)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := MachineState.readWord s.memory offset.toNat :: rest
      pc := s.pc.succ
      activeWords := s.activeWordsAfterUInt256 offset.toNat 32 } := by
  let cost := Gas.mloadTotal s offset
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.mloadTotal,
    State.activeWordsAfterUInt256] using
    StepRunning.mload (withGas s gas) offset rest hop hstack hgas hcap

def mstore8 {s : State} (offset value : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .MSTORE8)
    (hstack : s.stack = offset :: value :: rest)
    (hcap : s.stack.length + Operation.pushArity .MSTORE8 ≤
      1024 + Operation.popArity .MSTORE8)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := rest
      pc := s.pc.succ
      memory := MachineState.writeBytes s.memory
        (ByteArray.mk #[UInt8.ofNat (value.toNat % 256)]) offset.toNat
      activeWords := s.activeWordsAfterUInt256 offset.toNat 1 } := by
  let cost := Gas.mstore8Total s offset
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.mstore8Total, State.activeWordsAfterUInt256] using
    StepRunning.mstore8 (withGas s gas) offset value rest hop hstack hgas hcap

@[simp] theorem mstore8_cost {s : State} (offset value : UInt256)
    (rest : List UInt256) (hop : s.decodedOp = some .MSTORE8)
    (hstack : s.stack = offset :: value :: rest) (hcap) (hrun) (hnp) :
    (mstore8 (s := s) offset value rest hop hstack hcap hrun hnp).cost =
      Gas.mstore8Total s offset := rfl

def mcopy {s : State} (destOff srcOff size : UInt256)
    (rest : List UInt256)
    (hop : s.decodedOp = some .MCOPY)
    (hstack : s.stack = destOff :: srcOff :: size :: rest)
    (hcap : s.stack.length + Operation.pushArity .MCOPY ≤
      1024 + Operation.popArity .MCOPY)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := rest
      pc := s.pc.succ
      memory := MachineState.writeBytes s.memory
        (MachineState.readPadded s.memory srcOff.toNat size.toNat)
        destOff.toNat
      activeWords := s.activeWordsAfterUInt256_2
        destOff.toNat size.toNat srcOff.toNat size.toNat } := by
  let cost := Gas.mcopyTotal s destOff srcOff size
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.mcopyTotal,
    State.activeWordsAfterUInt256_2] using
    StepRunning.mcopy (withGas s gas) destOff srcOff size rest
      hop hstack hgas hcap

def jump {s : State} (dest : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .JUMP)
    (hstack : s.stack = dest :: rest)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
    (hcap : s.stack.length + Operation.pushArity .JUMP ≤
      1024 + Operation.popArity .JUMP)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := rest, pc := dest } := by
  let cost := Gas.baseCost s.fork .JUMP
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.jump (withGas s gas) dest rest hop hgas hstack hvalid hcap

def jumpiTaken {s : State} (dest cond : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .JUMPI)
    (hstack : s.stack = dest :: cond :: rest)
    (hcond : UInt256.isTrue cond)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
    (hcap : s.stack.length + Operation.pushArity .JUMPI ≤
      1024 + Operation.popArity .JUMPI)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := rest, pc := dest } := by
  let cost := Gas.baseCost s.fork .JUMPI
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.jumpi_taken (withGas s gas) dest cond rest hop hgas hstack
      hcond hvalid hcap

def jumpiNotTaken {s : State} (dest cond : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .JUMPI)
    (hstack : s.stack = dest :: cond :: rest)
    (hcond : ¬ UInt256.isTrue cond)
    (hcap : s.stack.length + Operation.pushArity .JUMPI ≤
      1024 + Operation.popArity .JUMPI)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .JUMPI
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.jumpi_notTaken (withGas s gas) dest cond rest hop hgas hstack
      hcond hcap

def return_ {s : State} (offset size : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .RETURN)
    (hstack : s.stack = offset :: size :: rest)
    (hcap : s.stack.length + Operation.pushArity .RETURN ≤
      1024 + Operation.popArity .RETURN)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      halt := .Returned
      hReturn := MachineState.readPadded s.memory offset.toNat size.toNat
      stack := rest
      activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat } := by
  let cost := Gas.returnTotal s offset size
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.returnTotal,
    State.activeWordsAfterUInt256] using
    StepRunning.return_ (withGas s gas) offset size rest hop hstack hgas hcap

@[simp] theorem return_cost {s : State} (offset size : UInt256)
    (rest : List UInt256) (hop : s.decodedOp = some .RETURN)
    (hstack : s.stack = offset :: size :: rest) (hcap) (hrun) (hnp) :
    (return_ (s := s) offset size rest hop hstack hcap hrun hnp).cost =
      Gas.returnTotal s offset size := rfl

end Challenge.EvmProof.GasStep
