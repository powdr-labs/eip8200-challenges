"""Emit the rounds-loop *iteration* lemma (bootstrap item 2).

One file, one artifact: the eight round block lemmas (re-emitted via
`emit_loop`), the control-tail block (spliced verbatim from `Ctrl.lean`
— same artifact, asserted), and a composed theorem chaining all nine
blocks with `runLocatedBlock_append`.

The composition tracks the eight stack expressions symbolically through
the eight rounds (exactly mirroring the per-round lemma conclusions), so
each intermediate state can be written *flat* — `{ s with ... }` of the
original state — and every side condition of block j+1 discharges by
`rfl`/`hrun` against block j's output, as demonstrated in `Two.lean`.
"""

import os
import emit_loop
import sha256gen4 as G
from sha256gen4 import woff, koff

WORK = os.path.dirname(os.path.abspath(__file__))
CYC = "abcdefgh"


def par(x):
    return x if " " not in x else f"({x})"


def track_rounds(count):
    """Mirror the emitter's per-round conclusion, but keep every stack entry
    a *constant-size* term: round j's two fresh working variables become
    defs `d{j}`/`h{j}` applied to the original atoms, with bodies that
    reference the earlier defs.  Raw substitution grows the expression tree
    ~2.4x per round (~12K tokens by round 7) and blows every downstream
    defeq check; with defs, each step lemma's unification unfolds exactly
    one definition level.  Returns (states, defs): the stack-entry lists
    after each round, and the (name, params, body) def list."""
    E = [f"S{k}" for k in range(8)]
    slots = list(CYC)
    states, defs = [], []
    for j in range(count):
        atoms = " ".join(
            [f"S{k}" for k in range(8)]
            + [x for i in range(j + 1) for x in (f"Kc{i}", f"Wt{i}")])
        ri = {r: k for k, r in enumerate(slots)}
        a, b, c, d, e, f, g, h = (E[ri[r]] for r in CYC)
        t1 = f"T1 {par(e)} {par(f)} {par(g)} {par(h)} Kc{j} Wt{j}"
        defs.append((f"d{j}", atoms, f"{par(d)} + {t1}"))
        defs.append((f"h{j}", atoms, f"{t1} + T2 {par(a)} {par(b)} {par(c)}"))
        E2 = list(E)
        E2[ri["d"]] = f"d{j} {atoms}"
        E2[ri["h"]] = f"h{j} {atoms}"
        E = E2
        slots = [CYC[(CYC.index(r) + 1) % 8] for r in slots]
        states.append(list(E))
    return states, defs


def stack_str(exprs, ptr):
    return ("[" + ",\n      ".join(f"ofUInt32 {par(x)}" for x in exprs)
            + f"] ++ {ptr} :: rest")


def state_str(pc, exprs, ptr):
    return (f"""{{ s with
        pc := UInt256.ofNat {pc}
        activeWords := UInt256.ofNat 140
        stack := {stack_str(exprs, ptr)} }}""")


def ctrl_text():
    src = open(os.path.join(WORK, "Ctrl.lean")).read()
    # slice pctrl + its doc comment + ctrl_continue, verbatim
    start = src.index("@[evmStep] def pctrl")
    end = src.index("\nend Ctrl")
    assert start < end
    return src[start:end] + "\n"


def emit(count=8):
    with_ctrl = count == 8
    core = emit_loop.emit("round", count)
    footer = "\nend Loop\n"
    assert core.endswith(footer), core[-40:]
    core = core[: -len(footer)]

    # pc boundaries of the round blocks, from the generator's marks
    code, gen = G.build()
    marks = [m for m in gen.marks if m[0] == "round"][:count]
    assert len(marks) == count
    p0s = [m[2] for m in marks]
    p1s = [m[3] for m in marks]
    assert p0s[0] == 912, p0s[0]
    for j in range(count - 1):
        assert p1s[j] == p0s[j + 1], (j, p1s[j], p0s[j + 1])
    if with_ctrl:
        assert p1s[7] == 1680, p1s[7]

    states, wdefs = track_rounds(count)
    S = " ".join(f"S{k}" for k in range(8))
    Ks = " ".join(f"Kc{j}" for j in range(count))
    Ws = " ".join(f"Wt{j}" for j in range(count))

    hyps = [f"""    (hk{j} : MachineState.readWord s.memory
      (UInt256.ofNat {koff(j)} + q).toNat = ofUInt32 Kc{j})
    (hw{j} : MachineState.readWord s.memory
      (UInt256.ofNat {woff(j)} + q).toNat = dbl (ofUInt32 Wt{j}))"""
            for j in range(count)]

    blocks = " ++ ".join([f"pround{j}" for j in range(count)]
                         + (["pctrl"] if with_ctrl else []))
    if with_ctrl:
        final = state_str(911, states[-1], "(UInt256.ofNat 256 + q)")
        ctrl_hyps = """    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + q) (UInt256.ofNat 2048)))
    (hcode : s.executionEnv.code = bytes)
"""
    else:
        final = state_str(p1s[-1], states[-1], "q")
        ctrl_hyps = ""

    name = "iter_continue" if with_ctrl else f"iter{count}"
    doc_tail = (' plus the control tail, in\nthe "continue" case: the group '
                "pointer `q` advances by 256 and control\nreturns to the loop "
                "head at 911") if with_ctrl else ""
    out = [core, ctrl_text() if with_ctrl else ""]

    out.append("""
/-! Round-output definitions.  `d{j}`/`h{j}` are round `j`'s two fresh
working variables (in FIPS terms the new `e` = d + T1 and the new
`a` = T1 + T2), as functions of the original eight inputs and the K/W
values consumed so far.  Keeping every stack entry an *application* of
these defs holds all iteration statements at constant size; each step
lemma's unification unfolds exactly one definition level. -/
""")
    for nm, atoms, body in wdefs:
        out.append(f"def {nm} ({atoms} : UInt32) : UInt32 :=\n  {body}\n")

    HOFF = """  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + q).toNat = k + q.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
"""

    def bounds(j):
        return f"""  have hbK : (UInt256.ofNat {koff(j)} + q).toNat + 32 ≤ 4480 := by
    rw [hoff {koff(j)} (by omega)]; omega
  have hbW : (UInt256.ofNat {woff(j)} + q).toNat + 32 ≤ 4480 := by
    rw [hoff {woff(j)} (by omega)]; omega
"""

    # Each chaining step is its own private theorem so it gets its own
    # heartbeat budget and, on failure, its own error position.
    kws = lambda j: " ".join([f"Kc{i}" for i in range(j + 1)]
                             + [f"Wt{i}" for i in range(j + 1)])
    out.append(f"""
private theorem step0 (s : State) ({S} Kc0 Wt0 : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 912)
    (hstack : s.stack =
      [{", ".join("ofUInt32 S" + str(k) for k in range(8))}] ++ q :: rest)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat {koff(0)} + q).toNat = ofUInt32 Kc0)
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat {woff(0)} + q).toNat = dbl (ofUInt32 Wt0)) :
    runLocatedBlock pround0 s =
      some {state_str(p1s[0], states[0], "q")} := by
{HOFF}{bounds(0)}  exact round0 s {S} Kc0 Wt0 q rest hcap hq haw hbK hbW hrun hpc hstack hk hw
""")
    us = "_ " * 12
    for j in range(1, count):
        out.append(f"""
private theorem step{j} (s : State) ({S} {kws(j)} : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792) (hrun : s.halt = .Running)
    (hk : MachineState.readWord s.memory
      (UInt256.ofNat {koff(j)} + q).toNat = ofUInt32 Kc{j})
    (hw : MachineState.readWord s.memory
      (UInt256.ofNat {woff(j)} + q).toNat = dbl (ofUInt32 Wt{j})) :
    runLocatedBlock pround{j}
      {state_str(p0s[j], states[j - 1], "q")} =
      some {state_str(p1s[j], states[j], "q")} := by
{HOFF}{bounds(j)}  exact round{j} {us}rest hcap hq rfl hbK hbW hrun rfl rfl hk hw
""")
    if with_ctrl:
        out.append(f"""
set_option maxHeartbeats 16000000 in
private theorem step8 (s : State) ({S} {kws(7)} : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + q) (UInt256.ofNat 2048)))
    (hcode : s.executionEnv.code = bytes)
    (hrun : s.halt = .Running) :
    runLocatedBlock pctrl
      {state_str(1680, states[7], "q")} =
      some {final} :=
  ctrl_continue {"_ " * 10}rest hcap hrun rfl hbr hcode rfl rfl
""")

    # the composed theorem is now only the append chain, with every step
    # applied to explicit arguments
    args0 = f"s {S} Kc0 Wt0 q rest hcap hq haw hrun hpc hstack hk0 hw0"
    step_apps = [f"step0 {args0}"]
    for j in range(1, count):
        step_apps.append(
            f"step{j} s {S} {kws(j)} q rest hcap hq hrun hk{j} hw{j}")
    if with_ctrl:
        step_apps.append(f"step8 s {S} {kws(7)} q rest hcap hbr hcode hrun")
    chain_lines = "\n".join(
        f"  refine runLocatedBlock_append _ _\n    ({app}) hrun ?_"
        for app in step_apps[:-1])
    chain = f"{chain_lines}\n  exact {step_apps[-1]}"
    out.append(f"""
set_option maxHeartbeats 64000000 in
/-- One full iteration of the eight-round loop{doc_tail}.  All inputs are
opaque; the memory reads are `q`-relative hypotheses on the *initial*
state, sound because the round blocks never write memory. -/
theorem {name} (s : State)
    ({S} : UInt32)
    ({Ks} : UInt32)
    ({Ws} : UInt32)
    (q : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hq : q.toNat ≤ 1792)
    (haw : s.activeWords = UInt256.ofNat 140)
{ctrl_hyps}    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 912)
    (hstack : s.stack =
      [{", ".join("ofUInt32 S" + str(k) for k in range(8))}] ++ q :: rest)
{chr(10).join(hyps)} :
    runLocatedBlock ({blocks}) s =
      some {final} := by
{chain}
""")
    return "".join(out) + "\nend Loop\n"


STEPS_HEADER = """import Rounds8
set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! The rounds-loop iteration: chaining the block lemmas of `Rounds8`.
Split from the artifact file so composition work recompiles in seconds
against `Rounds8.olean` instead of re-elaborating the blocks (~12 min). -/

namespace Loop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word Challenge.Sha256.Fast
open EvmSemantics.Crypto.Sha256

"""


def emit_split(count=8):
    """Write Rounds8.lean (stable: artifact + block lemmas + ctrl + defs)
    and IterSteps.lean (volatile: step lemmas + iter_continue)."""
    whole = emit(count)
    marker = "\nprivate theorem step0 "
    cut = whole.index(marker)
    # the set_option/comment block introducing the steps stays with them
    stable = whole[:cut] + "\nend Loop\n"
    steps = STEPS_HEADER + whole[cut + 1:]
    # `private` would hide the steps from importers of IterSteps itself,
    # which is fine; but wfOp-style helpers are not referenced here.
    return stable, steps


if __name__ == "__main__":
    import sys
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    if sys.argv[1] == "--split":
        stable, steps = emit_split(n)
        open("Rounds8.lean", "w").write(stable)
        open("IterSteps.lean", "w").write(steps)
        print("emitted Rounds8.lean and IterSteps.lean with", n, "rounds")
    else:
        open(sys.argv[1], "w").write(emit(n))
        print("emitted", sys.argv[1], "with", n, "rounds")
