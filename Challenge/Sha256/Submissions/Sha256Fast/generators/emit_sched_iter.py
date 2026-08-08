"""Emit the schedule-loop *iteration* lemma as a single block (item 2, sched half).

Unlike the rounds loop, the sched steps within a group are memory-coupled:
step j+2 reads the slot step j wrote (W[t-2]), and step 7 reads step 0's
write (W[t-7]).  Composing the existing weak per-step lemmas would need
explicit read-through-write bookkeeping at every seam, so instead the whole
iteration (8 steps, optionally + the inline control tail) is proved as ONE
`evm_block` over one contiguous path: within a block, read-after-write
reduces by `readWord_writeWord` (hit) and `readWord_writeWord_disjoint_rel`
(miss, the new pointer-relative lemma in `Sha256Fast.Block`), and every
stored value is a function of opaque W variables, so terms do not compound.

The conclusion names the full end state, memory as `k` nested `writeBytes`
layers.  `emit(count, with_ctrl)`: small `count` without ctrl is the probe
mode used to pin down the stepper's syntactic normal form.
"""

import os
import sha256gen4 as G
from sha256gen4 import woff
from emit_probe import disassemble, lean_located, lean_instr

WORK = os.path.dirname(os.path.abspath(__file__))

HEADER = '''import Challenge.Sha256.Submissions.Sha256Fast.Proofs.Rounds8
set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
set_option linter.unusedVariables false

/-! One iteration of the schedule loop of the loop-of-8 SHA-256 artifact,
proved as a single block. -/

namespace Loop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word Challenge.Sha256.Fast
open EvmSemantics.Crypto.Sha256
'''


def par(x):
    return x if " " not in x else f"({x})"


def sched_values(count):
    """The value stored by each step, over opaque V0..V15 (the sixteen
    W slots preceding the group, u-relative)."""
    N = []
    for j in range(count):
        x2 = f"V{14 + j}" if 14 + j < 16 else N[j - 2]
        x7 = f"V{9 + j}" if 9 + j < 16 else N[j - 7]
        x15 = f"V{1 + j}"
        x16 = f"V{j}"
        N.append(f"smallSigma1 {par(x2)} + {par(x7)} + smallSigma0 {par(x15)} + {par(x16)}")
    return N


def external_reads(count):
    """u-relative W slots (< 16) each step reads from the pre-iteration
    memory, deduplicated, in first-use order."""
    seen, order = set(), []
    for j in range(count):
        for t in (14 + j, 9 + j, 1 + j, j):
            if t < 16 and t not in seen:
                seen.add(t)
                order.append(t)
    return order


def emit(count=8, with_ctrl=None):
    if with_ctrl is None:
        with_ctrl = count == 8
    assert 1 <= count <= 8
    code, gen = G.build()
    instrs = disassemble(code)
    pcs, p = [], 0
    for kind, x, y in instrs:
        pcs.append(p)
        p += (1 + x) if kind == "push" else 1
    loc = [lean_located(i, ins) for i, ins in enumerate(instrs)]

    marks = [m for m in gen.marks if m[0] == "sched"][:count]
    assert len(marks) == count
    p0 = marks[0][2]
    p_end = marks[-1][3]
    for k in range(count - 1):
        assert marks[k][3] == marks[k + 1][2]
    i0, i1 = pcs.index(p0), pcs.index(p_end)

    if with_ctrl:
        # the inline control tail: PUSH 256, ADD, PUSH 1536, DUP2, LT,
        # PUSH <sched>, JUMPI
        tail = instrs[i1:i1 + 7]
        kinds = [t[0] for t in tail]
        assert kinds == ["push", "op", "push", "dup", "op", "push", "op"], kinds
        assert tail[1][1] == "ADD" and tail[4][1] == "LT" and tail[6][1] == "JUMPI", tail
        assert tail[2][1:] == (2, 1536), tail[2]
        sched_dest = tail[5][2]
        assert sched_dest == p0 - 1, (sched_dest, p0)  # JUMPDEST right before sched0
        assert instrs[pcs.index(sched_dest)][1] == "JUMPDEST"
        branch_index = i1 + 6
        i1 += 6
        # instruction index of the JUMPDEST, for the isValidJumpDest proof
        dest_index = pcs.index(sched_dest)

    # Reuse the exact artifact from Rounds8.  PR 20 originally repeated all
    # 1,475 instructions here, which made the two iteration modules impossible
    # to import together and inflated this file's elaboration cost.
    out = [HEADER]
    out.append("""private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
""")
    name = "psched_compute" if with_ctrl else f"psched_probe{count}"
    if with_ctrl:
        # Keep the cost proof compact by exposing the eight natural schedule
        # steps and the loop-test setup as separate paths.  The functional
        # block remains their exact concatenation.
        pieces = []
        for j, mark in enumerate(marks):
            j0, j1 = pcs.index(mark[2]), pcs.index(mark[3])
            piece = f"psched_costStep{j}"
            pieces.append(piece)
            out.append(f"@[evmStep] def {piece} : List (Located art .Osaka) :=\n"
                       "  [" + ",\n   ".join(loc[j0:j1]) + "]\n")
        pieces.append("psched_costControlSetup")
        out.append("@[evmStep] def psched_costControlSetup : List (Located art .Osaka) :=\n"
                   "  [" + ",\n   ".join(loc[pcs.index(marks[-1][3]):i1]) + "]\n")
        out.append("@[evmStep] def psched_compute : List (Located art .Osaka) :=\n"
                   "  [" + ",\n   ".join(loc[i0:i1]) + "]\n")
    else:
        out.append(f"@[evmStep] def {name} : List (Located art .Osaka) :=\n"
                   "  [" + ",\n   ".join(loc[i0:i1]) + "]\n")
    if with_ctrl:
        out.append("@[evmStep] def psched_branch : List (Located art .Osaka) :=\n"
                   f"  [{loc[branch_index]}]\n")

    N = sched_values(count)
    ext = external_reads(count)
    Vs = " ".join(f"V{t}" for t in ext)

    read_hyps = "\n".join(
        f"""    (hv{t} : MachineState.readWord s.memory
      (UInt256.ofNat {woff(t)} + u).toNat = dbl (ofUInt32 V{t}))"""
        for t in ext)

    # nested writeBytes, oldest innermost
    mem = "s.memory"
    for j in range(count):
        mem = (f"MachineState.writeBytes {par(mem)}\n          "
               f"(Data.Bytes.natToBytesPadded (dbl (ofUInt32 ({N[j]}))).toNat 32)\n          "
               f"(UInt256.ofNat {woff(16 + j)} + u).toNat")
    thm = "sched_iter_compute" if with_ctrl else f"sched_probe{count}"
    if with_ctrl:
        end_pc = pcs[branch_index]
        end_stack = ("[UInt256.ofNat 294, UInt256.lt "
                     "(UInt256.ofNat 256 + u) (UInt256.ofNat 1536), "
                     "UInt256.ofNat 256 + u] ++ rest")
        ctrl_hyps = ""
    else:
        end_pc = p_end
        end_stack = "u :: rest"
        ctrl_hyps = ""

    # every u-relative offset the block touches, for the watermark bounds
    offs = sorted({woff(t) for t in ext} | {woff(16 + j) for j in range(count)})
    bound_haves = "\n".join(
        f"""  have hb{o} : (UInt256.ofNat {o} + u).toNat + 32 ≤ 4480 := by
    rw [hoff {o} (by omega)]; omega""" for o in offs)

    out.append(f"""
/-- One iteration of the schedule loop{", through the branch setup" if with_ctrl else f" truncated to {count} step(s) (probe)"}:
the eight W slots of the group are computed and stored from the sixteen
preceding slots, all addresses relative to the group pointer `u`. -/
theorem {thm} (s : State)
    ({Vs} : UInt32)
    (u : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hu : u.toNat ≤ 1280)
    (haw : s.activeWords = UInt256.ofNat 140)
{ctrl_hyps}    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat {p0})
    (hstack : s.stack = u :: rest)
{read_hyps} :
    runLocatedBlock {name} s =
      some {{ s with
        pc := UInt256.ofNat {end_pc}
        activeWords := UInt256.ofNat 140
        memory := {mem}
        stack := {end_stack} }} := by
  have hoff : ∀ k : Nat, k ≤ 2656 → (UInt256.ofNat k + u).toNat = k + u.toNat := by
    intro k hk
    rw [word_toNat_add, word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
{bound_haves}
  clear hoff
""")
    out.append("""  evm_block hcap
  and_intros <;>
    first
    | rfl
    | ac_rfl
    | omega
    | (repeat' first
        | rfl
        | (apply congrArg₂ (fun x y => MachineState.writeBytes x y _))
        | (apply congrArg (fun n => Data.Bytes.natToBytesPadded n 32))
        | (apply congrArg UInt256.toNat)
        | (apply congrArg dbl)
        | (apply congrArg ofUInt32)
        | ac_rfl)
""")
    if with_ctrl:
        out.append(f"""
/-- Take the schedule-loop back edge after a non-final group. -/
theorem sched_branch_continue (s : State) (u : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = bytes) (hrun : s.halt = .Running)
    (hpc : s.pc = UInt256.ofNat {pcs[branch_index]})
    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536)))
    (hstack : s.stack =
      [UInt256.ofNat 294,
       UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536),
       UInt256.ofNat 256 + u] ++ rest) :
    runLocatedBlock psched_branch s =
      some {{ s with
        pc := UInt256.ofNat {sched_dest}
        stack := (UInt256.ofNat 256 + u) :: rest }} := by
  have hdest : Decode.isValidJumpDest bytes {sched_dest} = true := by
    have h := ProgramArtifact.isValidJumpDest_index art {dest_index} (by rfl)
    have hpcd : art.instructionPC {dest_index} = {sched_dest} := by rfl
    rw [hpcd] at h
    exact h
  evm_block hcap

/-- Fall through after the sixth and final schedule group. -/
theorem sched_branch_exit (s : State) (u : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running)
    (hpc : s.pc = UInt256.ofNat {pcs[branch_index]})
    (hbr : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536)) = false)
    (hstack : s.stack =
      [UInt256.ofNat 294,
       UInt256.lt (UInt256.ofNat 256 + u) (UInt256.ofNat 1536),
       UInt256.ofNat 256 + u] ++ rest) :
    runLocatedBlock psched_branch s =
      some {{ s with
        pc := UInt256.ofNat 884
        stack := (UInt256.ofNat 256 + u) :: rest }} := by
  evm_block hcap
""")
    return "".join(out) + "\nend Loop\n"


if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    open(path, "w").write(emit(n))
    print("emitted", path, "with", n, "sched steps")
