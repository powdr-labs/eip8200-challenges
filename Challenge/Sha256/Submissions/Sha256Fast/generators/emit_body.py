"""Emit the straight-line seams around Sha256Fast's two inner loops."""

import sha256gen4 as G
from emit_probe import disassemble, lean_located


HEADER = '''import Challenge.Sha256.Submissions.Sha256Fast.Proofs.SchedIter

set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace Loop.Body

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open YulEvmCompiler Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.EvmProof.Word Challenge.Sha256.Fast

private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
'''


def path(name, located, start, stop):
    return (f"@[evmStep] def {name} : List (Located Loop.art .Osaka) :=\n  [" +
            ",\n   ".join(located[start:stop]) + "]\n")


def write_initial_memory():
    memory = "s.memory"
    for j in range(16):
        value = ("dbl (UInt256.shiftRight "
                 f"(MachineState.readWord s.memory {G.SCR + 4 * j}) "
                 "(UInt256.ofNat 224))")
        memory = (f"MachineState.writeBytes ({memory})\n"
                  f"          (Data.Bytes.natToBytesPadded ({value}).toNat 32)\n"
                  f"          {G.woff(j)}")
    return memory


def emit():
    code, gen = G.build()
    instructions = disassemble(code)
    located = [lean_located(i, instruction)
               for i, instruction in enumerate(instructions)]
    out = [HEADER]

    # Enter the subroutine, load W[0..15], push u=0, and consume the schedule
    # loop's JUMPDEST.  The next instruction is sched step 0 at PC 295.
    out.append(path("initialSchedulePath", located, 2, 133))
    memory = write_initial_memory()
    out.append(f'''
/-- The subroutine's straight-line prefix reads the sixteen big-endian words
from the staged block and stores their doubled representations in W[0..15]. -/
theorem run_initialSchedule (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 4)
    (hstack : s.stack = returnDest :: rest) :
    runLocatedBlock initialSchedulePath s =
      some {{ s with
        pc := UInt256.ofNat 295
        activeWords := UInt256.ofNat 140
        memory := {memory}
        stack := UInt256.ofNat 0 :: returnDest :: rest }} := by
  evm_block hcap
''')

    # Back edges target the JUMPDEST immediately before each loop body.  Keep
    # these one-instruction seams explicit so the group evaluators can start
    # at their first real instruction.
    out.append(path("scheduleHeadPath", located, 132, 133))
    out.append('''
theorem run_scheduleHead (s : State) (u : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 294)
    (hstack : s.stack = u :: rest) :
    runLocatedBlock scheduleHeadPath s =
      some { s with pc := UInt256.ofNat 295 } := by
  evm_block hcap
''')

    # After the sixth schedule group the conditional branch falls through;
    # POP u, push q=0, load h..a, and consume the rounds JUMPDEST.
    out.append(path("prepareRoundsPath", located, 516, 535))
    out.append('''
/-- Leave the schedule loop and load the current chaining state into the eight
fixed working stack slots. -/
theorem run_prepareRounds (s : State)
    (A B C D E F G H returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 884)
    (hstack : s.stack = UInt256.ofNat 1536 :: returnDest :: rest)
    (hA : MachineState.readWord s.memory 32 = A)
    (hB : MachineState.readWord s.memory 64 = B)
    (hC : MachineState.readWord s.memory 96 = C)
    (hD : MachineState.readWord s.memory 128 = D)
    (hE : MachineState.readWord s.memory 160 = E)
    (hF : MachineState.readWord s.memory 192 = F)
    (hG : MachineState.readWord s.memory 224 = G)
    (hH : MachineState.readWord s.memory 256 = H) :
    runLocatedBlock prepareRoundsPath s =
      some { s with
        pc := UInt256.ofNat 912
        activeWords := UInt256.ofNat 140
        stack := [A, B, C, D, E, F, G, H, UInt256.ofNat 0,
          returnDest] ++ rest } := by
  evm_block hcap

@[evmStep] def roundsHeadPath : List (Located Loop.art .Osaka) :=
  [⟨534, Instr.op (Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)),
    by rfl, wfOp (by decide) trivial rfl⟩]

theorem run_roundsHead (s : State)
    (stack : List UInt256) (hcap : stack.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 911)
    (hstack : s.stack = stack) :
    runLocatedBlock roundsHeadPath s =
      some { s with pc := UInt256.ofNat 912 } := by
  evm_block hcap

end Loop.Body
''')
    return "".join(out)


if __name__ == "__main__":
    import sys
    with open(sys.argv[1], "w") as output:
        output.write(emit())
