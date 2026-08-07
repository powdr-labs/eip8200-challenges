"""Emit a chained sequence of compression-round blocks as Lean.

Design note.  Each block lemma is stated over *opaque* input words `S0..S7`,
never over the previous round's expressions.  That keeps every block proof the
same size no matter how deep in the chain it sits — the alternative (unfolding
the previous rounds' definitions into the goal) makes round `t`'s term nest `t`
deep and blows simp's step budget by round 4.

The chain then instantiates each lemma with the previous round's output
*names* (`rNa`, `rNe` definitions), so the composed statement stays flat and
the `hstack` side conditions hold by `rfl`.
"""

import sha256gen3 as G
from asm import Asm
from emit_probe import disassemble, lean_located, lean_instr
from sha256gen3 import K, woff

HEADER = '''import Sha256Fast.Block
set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! {n} chained compression rounds, generated.  Each round is one `evm_block`
over opaque inputs; the chain is `runLocatedBlock_append`. -/

namespace Rounds
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word Challenge.Sha256.Fast
open EvmSemantics.Crypto.Sha256

def T1 (E F G H Kc Wt : UInt32) : UInt32 := H + bigSigma1 E + Ch E F G + Kc + Wt
def T2 (A B C : UInt32) : UInt32 := bigSigma0 A + Maj A B C
'''


def emit(nrounds: int) -> str:
    g = G.Gen()
    g.a = Asm()
    rounds = []
    for t in range(nrounds):
        slots = list(g.slots)
        pc0 = g.a._pos
        i0 = len(disassemble(g.a.assemble()))
        g.round(t)
        rounds.append((i0, len(disassemble(g.a.assemble())), pc0,
                       g.a._pos, slots, t))

    instrs = disassemble(g.a.assemble())
    loc = [lean_located(i, ins) for i, ins in enumerate(instrs)]
    out = [HEADER.format(n=nrounds)]
    # instruction list as a concatenation of per-round blocks: indexing and
    # prefix-taking then cost O(#blocks + blocksize) instead of O(n)
    for i0, i1, _, _, _, t in rounds:
        out.append(f"@[evmStep] def blk{t} : List Instr :=\n[" +
                   ",\n ".join(lean_instr(x) for x in instrs[i0:i1]) + "]\n")
    out.append("@[evmStep] def instrs : List Instr :=\n  " +
               " ++ ".join(f"blk{t}" for _, _, _, _, _, t in rounds) + "\n")
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
    for i0, i1, _, _, _, t in rounds:
        out.append(f"@[evmStep] def p{t} : List (Located art .Osaka) :=\n  [" +
                   ",\n   ".join(loc[i0:i1]) + "]\n")

    S = [f"S{i}" for i in range(8)]
    for i0, i1, pc0, pc1, slots, t in rounds:
        ri = {r: i for i, r in enumerate(slots)}
        a, b, c, d, e, f, gg, h = (S[ri[r]] for r in "abcdefgh")
        t1 = f"T1 {e} {f} {gg} {h} 0x{K[t]:08x} Wt"
        outs = []
        for i in range(8):
            if i == ri['d']:
                outs.append(f"ofUInt32 ({d} + {t1})")
            elif i == ri['h']:
                outs.append(f"ofUInt32 ({t1} + T2 {a} {b} {c})")
            else:
                outs.append(f"ofUInt32 S{i}")
        wm = woff(t) // 32 + 1
        out.append(f"""/-- Round {t}: slot permutation `{''.join(slots)}`. -/
theorem step{t} (s : State) ({' '.join(S)} Wt : UInt32) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hpc : s.pc = UInt256.ofNat {pc0})
    (hstack : s.stack = [{', '.join('ofUInt32 ' + x for x in S)}] ++ rest)
    (hmem : MachineState.readWord s.memory {woff(t)} = dbl (ofUInt32 Wt)) :
    runLocatedBlock p{t} s =
      some {{ s with
        pc := UInt256.ofNat {pc1}
        activeWords := UInt256.ofNat (s.activeWords.toNat.max {wm})
        stack := [{', '.join(outs)}] ++ rest }} := by
  simp only [T1, T2]
  evm_block hcap
  refine ⟨?_, ?_⟩ <;> ac_rfl
""")
    return "\n".join(out) + "\nend Rounds\n"


if __name__ == "__main__":
    import sys
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    open(sys.argv[2], "w").write(emit(n))
    print("emitted", n, "rounds")
