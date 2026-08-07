"""Emit block lemmas for the loop-of-8 artifact (`sha256gen4`).

Both loop bodies address memory off a pointer held on the stack (`q = 256i` for
the round groups, `u = 256g` for the schedule groups), so the block lemmas
quantify over that pointer and take the memory contents at pointer-relative
addresses as hypotheses.  Everything else is as in the unrolled case: opaque
input words, whole end state named, `evm_block` then `ac_rfl`.
"""

import sha256gen4 as G
from emit_probe import disassemble, lean_located, lean_instr
from sha256gen4 import woff, koff

HEADER = '''import Sha256Fast.Block
set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! Block lemmas for the loop-of-8 SHA-256 artifact.  Eight round shapes and
eight schedule shapes cover the whole compression, because each loop body is
executed with only the pointer changing. -/

namespace Loop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word Challenge.Sha256.Fast
open EvmSemantics.Crypto.Sha256

def T1 (E F G H Kc Wt : UInt32) : UInt32 := H + bigSigma1 E + Ch E F G + Kc + Wt
def T2 (A B C : UInt32) : UInt32 := bigSigma0 A + Maj A B C
'''


def instr_index_at(pcs, pos):
    return pcs.index(pos)


def emit(which="round", count=8):
    code, gen = G.build()
    instrs = disassemble(code)
    # byte offset of each instruction
    pcs, p = [], 0
    for kind, x, y in instrs:
        pcs.append(p)
        p += (1 + x) if kind == "push" else 1
    pcs.append(p)
    loc = [lean_located(i, ins) for i, ins in enumerate(instrs)]

    out = [HEADER]
    out.append("@[evmStep] def instrs : List Instr :=\n[" +
               ",\n ".join(lean_instr(x) for x in instrs) + "]\n")
    out.append("@[evmStep] def bytes : ByteArray := assemble instrs\n")
    out.append("""@[evmStep] def art : ProgramArtifact where
  code := bytes
  instructions := instrs
  assembly_eq := rfl

private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
""")

    marks = [m for m in gen.marks if m[0] == which][:count]
    S = [f"S{i}" for i in range(8)]
    slots = list("abcdefgh")
    for kind, j, p0, p1 in marks:
        i0, i1 = instr_index_at(pcs, p0), instr_index_at(pcs, p1)
        out.append(f"@[evmStep] def p{kind}{j} : List (Located art .Osaka) :=\n"
                   "  [" + ",\n   ".join(loc[i0:i1]) + "]\n")
        if kind == "round":
            ri = {r: k for k, r in enumerate(slots)}
            a, b, c, d, e, f, gg, h = (S[ri[r]] for r in "abcdefgh")
            t1 = f"T1 {e} {f} {gg} {h} Kc Wt"
            res = []
            for k in range(8):
                if k == ri['d']:
                    res.append(f"ofUInt32 ({d} + {t1})")
                elif k == ri['h']:
                    res.append(f"ofUInt32 ({t1} + T2 {a} {b} {c})")
                else:
                    res.append(f"ofUInt32 S{k}")
            out.append(f"""/-- Round {j} of the eight-round loop body (permutation `{''.join(slots)}`).
`q` is the group pointer; `K` and `W` are read at `q`-relative addresses. -/
theorem round{j} (s : State) ({' '.join(S)} Kc Wt : UInt32) (q : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (haw : s.activeWords = UInt256.ofNat 140)
    (hbk : (UInt256.ofNat {koff(j)} + q).toNat + 32 ≤ 4480)
    (hbw : (UInt256.ofNat {woff(j)} + q).toNat + 32 ≤ 4480)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat {p0})
    (hstack : s.stack =
      [{', '.join('ofUInt32 ' + x for x in S)}] ++ q :: rest)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat {koff(j)} + q).toNat = ofUInt32 Kc)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat {woff(j)} + q).toNat = dbl (ofUInt32 Wt)) :
    runLocatedBlock p{kind}{j} s =
      some {{ s with
        pc := UInt256.ofNat {p1}
        activeWords := UInt256.ofNat 140
        stack := [{', '.join(res)}] ++ q :: rest }} := by
  simp only [T1, T2]
  evm_block hcap
  and_intros <;>
    first | ac_rfl | (apply congrArg UInt256.ofNat; omega) | omega
""")
            cyc = "abcdefgh"
            slots = [cyc[(cyc.index(r) + 1) % 8] for r in slots]
        else:
            # schedule step j of the eight-step body: W[16+8g+j] from four
            # earlier slots, every address relative to the group pointer u.
            out.append(f"""/-- Schedule step {j} of the eight-step loop body.  `u` is the group
pointer; the four reads and the one write are all `u`-relative. -/
theorem sched{j} (s : State) (W2 W7 W15 W16 : UInt32) (u : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hu : u.toNat ≤ 1280) (haw : s.activeWords = UInt256.ofNat 140)
    (hb2 : (UInt256.ofNat {woff(14 + j)} + u).toNat + 32 ≤ 4480)
    (hb7 : (UInt256.ofNat {woff(9 + j)} + u).toNat + 32 ≤ 4480)
    (hb15 : (UInt256.ofNat {woff(1 + j)} + u).toNat + 32 ≤ 4480)
    (hb16 : (UInt256.ofNat {woff(0 + j)} + u).toNat + 32 ≤ 4480)
    (hbt : (UInt256.ofNat {woff(16 + j)} + u).toNat + 32 ≤ 4480)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat {p0})
    (hstack : s.stack = u :: rest)
    (h2 : MachineState.readWord s.memory
      (UInt256.ofNat {woff(14 + j)} + u).toNat = dbl (ofUInt32 W2))
    (h7 : MachineState.readWord s.memory
      (UInt256.ofNat {woff(9 + j)} + u).toNat = dbl (ofUInt32 W7))
    (h15 : MachineState.readWord s.memory
      (UInt256.ofNat {woff(1 + j)} + u).toNat = dbl (ofUInt32 W15))
    (h16 : MachineState.readWord s.memory
      (UInt256.ofNat {woff(0 + j)} + u).toNat = dbl (ofUInt32 W16)) :
    (runLocatedBlock p{kind}{j} s).map
        (fun t => MachineState.readWord t.memory
          (UInt256.ofNat {woff(16 + j)} + u).toNat) =
      some (dbl (ofUInt32 (smallSigma1 W2 + W7 + smallSigma0 W15 + W16))) := by
  evm_block hcap
  apply congrArg dbl
  apply congrArg ofUInt32
  ac_rfl
""")
    return "\n".join(out) + "\nend Loop\n"


if __name__ == "__main__":
    import sys
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    open(sys.argv[1], "w").write(emit("round", n))
    print("emitted", n, "round blocks")
