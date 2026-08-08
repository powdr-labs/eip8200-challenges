"""Emit straight-line execution lemmas for Sha256Fast's driver and fold."""

import sha256gen4 as G
from emit_probe import disassemble, lean_located


HEADER = '''import Challenge.Sha256.Submissions.Sha256Fast.Proofs.Body
import YulEvmCompiler.BytesLemmas

set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverBlocks

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open YulEvmCompiler Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.EvmProof.Word Challenge.Sha256.Fast

private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
'''


def path(name, located, indices):
    body = ",\n   ".join(located[i] for i in indices)
    return f"@[evmStep] def {name} : List (Located Loop.art .Osaka) :=\n  [{body}]\n"


def write_word(memory, address, value):
    return (f"MachineState.writeBytes ({memory})\n"
            f"          (Data.Bytes.natToBytesPadded ({value}).toNat 32)\n"
            f"          {address}")


def initialized_memory(base="s.memory"):
    memory = base
    for i, value in enumerate(G.H0):
        memory = write_word(memory, G.HB + 32 * i, f"UInt256.ofNat {value}")
    for i, value in enumerate(G.K):
        memory = write_word(memory, G.KB + 32 * i, f"UInt256.ofNat {value}")
    return memory


def hash_memory(base="s.memory"):
    memory = base
    for i, value in enumerate(G.H0):
        memory = write_word(memory, G.HB + 32 * i, f"UInt256.ofNat {value}")
    return memory


def constant_chunk_memory(chunk, base="s.memory"):
    memory = base
    for j in range(8):
        i = 8 * chunk + j
        memory = write_word(memory, G.KB + 32 * i, f"UInt256.ofNat {G.K[i]}")
    return memory


def folded_memory(base="s.memory"):
    memory = base
    names = list("ABCDEFGH")
    saved = list("H0 H1 H2 H3 H4 H5 H6 H7".split())
    for i, (work, old) in enumerate(zip(names, saved)):
        # The EVM evaluates the working word first and then the saved hash word.
        # Keeping that operand order makes each generated block theorem reduce
        # definitionally; the functional proof later uses commutativity.
        value = f"ofUInt32 ({work} + {old})"
        memory = write_word(memory, G.HB + 32 * i, value)
    return memory


def emit():
    code, _ = G.build()
    located = [lean_located(i, ins) for i, ins in enumerate(disassemble(code))]
    out = [HEADER]

    init_composition = "hashMemory memory"
    for chunk in range(8):
        init_composition = f"constantMemory{chunk} ({init_composition})"
    constant_defs = "\n\n".join(
        f"def constantMemory{chunk} (memory : ByteArray) : ByteArray :=\n  " +
        constant_chunk_memory(chunk, "memory")
        for chunk in range(8))
    out.append(f'''
def hashMemory (memory : ByteArray) : ByteArray :=
  {hash_memory("memory")}

{constant_defs}

def initializedMemory (memory : ByteArray) : ByteArray :=
  {init_composition}

def foldedMemory (memory : ByteArray)
    (A B C D E F G H H0 H1 H2 H3 H4 H5 H6 H7 : UInt32) : ByteArray :=
  {folded_memory("memory")}
''')

    work_names = list("ABCDEFGH")
    old_names = list("H0 H1 H2 H3 H4 H5 H6 H7".split())
    pcs = [1696, 1709, 1722, 1735, 1748, 1761, 1774, 1787]
    for i, (work, old) in enumerate(zip(work_names, old_names)):
        start = 1089 + 7 * i
        stop = start + (9 if i == 7 else 7)
        out.append(path(f"feedForward{i}Path", located, range(start, stop)))
        input_words = ", ".join(f"ofUInt32 {x}" for x in work_names[i:])
        input_stack = f"[{input_words}, UInt256.ofNat 2048, returnDest] ++ rest"
        next_words = ", ".join(f"ofUInt32 {x}" for x in work_names[i + 1:])
        if i == 7:
            output_pc = "returnDest"
            output_stack = "rest"
        else:
            output_pc = f"UInt256.ofNat {pcs[i + 1]}"
            output_stack = f"[{next_words}, UInt256.ofNat 2048, returnDest] ++ rest"
        ret_hyp = ("    (hcode : s.executionEnv.code = Loop.bytes)\n"
                   "    (hret : Decode.isValidJumpDest Loop.bytes returnDest.toNat = true)\n"
                   if i == 7 else "")
        cap_type = "999" if i == 7 else "1000"
        cap_setup = ("  have hcap' : rest.length < 1000 := by omega\n"
                     "  have hret' : Decode.isValidJumpDest "
                     "(YulEvmCompiler.assemble Loop.instrs) returnDest.toNat = true := by\n"
                     "    simpa [Loop.bytes] using hret\n"
                     if i == 7 else "")
        cap_arg = "hcap'" if i == 7 else "hcap"
        out.append(f'''
theorem run_feedForward{i} (s : State) ({work} {old} : UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < {cap_type}) (haw : s.activeWords = UInt256.ofNat 140)
{ret_hyp}    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat {pcs[i]})
    (hstack : s.stack = {input_stack})
    (hh : MachineState.readWord s.memory {32 * (i + 1)} = ofUInt32 {old}) :
    runLocatedBlock feedForward{i}Path s =
      some {{ s with pc := {output_pc}
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (ofUInt32 ({work} + {old})).toNat 32)
          {32 * (i + 1)}
        stack := {output_stack} }} := by
{cap_setup}  evm_block {cap_arg}{' <;> simp only [hret\']' if i == 7 else ''}
''')

    # Split initialization into small proof blocks.  A monolithic 72-store
    # symbolic theorem is equivalent but creates a prohibitively large term.
    out.append(path("initializeEntryPath", located, [0, 1]))
    out.append('''
theorem run_initializeEntry (s : State)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hmain : Decode.isValidJumpDest Loop.bytes 1804 = true)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 0)
    (hstack : s.stack = []) :
    runLocatedBlock initializeEntryPath s =
      some { s with pc := UInt256.ofNat 1804 } := by
  have hmain' : Decode.isValidJumpDest
      (YulEvmCompiler.assemble Loop.instrs) 1804 = true := by
    simpa [Loop.bytes] using hmain
  evm_block <;> simp only [hmain']
''')

    out.append(path("initializeHashPath", located, range(1147, 1173)))
    out.append('''
theorem run_initializeHash (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1804)
    (haw : s.activeWords = UInt256.ofNat 0) (hstack : s.stack = [])
    (hn : UInt256.ofNat s.executionEnv.calldata.size = n) :
    runLocatedBlock initializeHashPath s =
      some { s with pc := UInt256.ofNat 1871
        activeWords := UInt256.ofNat 9
        memory := hashMemory s.memory
        stack := [n] } := by
  evm_block <;> simp [hashMemory, word_toNat_ofNat]
''')

    chunk_pcs = [1871, 1943, 2015, 2087, 2159, 2231, 2303, 2375, 2447]
    chunk_words = [9, 84, 92, 100, 108, 116, 124, 132, 140]
    for chunk in range(8):
        start = 1173 + 24 * chunk
        out.append(path(f"initializeConstants{chunk}Path", located,
                        range(start, start + 24)))
        out.append(f'''
theorem run_initializeConstants{chunk} (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat {chunk_pcs[chunk]})
    (haw : s.activeWords = UInt256.ofNat {chunk_words[chunk]})
    (hstack : s.stack = [n]) :
    runLocatedBlock initializeConstants{chunk}Path s =
      some {{ s with pc := UInt256.ofNat {chunk_pcs[chunk + 1]}
        activeWords := UInt256.ofNat {chunk_words[chunk + 1]}
        memory := constantMemory{chunk} s.memory
        stack := [n] }} := by
  evm_block <;> simp [constantMemory{chunk}, word_toNat_ofNat]
''')

    out.append(path("initializeDriverPath", located, range(1365, 1377)))
    out.append('''
theorem run_initializeDriver (s : State) (n : UInt256)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2447)
    (haw : s.activeWords = UInt256.ofNat 140) (hstack : s.stack = [n]) :
    runLocatedBlock initializeDriverPath s =
      some { s with pc := UInt256.ofNat 2464
        stack := [UInt256.ofNat 2491,
          UInt256.isZero (UInt256.shiftLeft
            (UInt256.shiftRight n (UInt256.ofNat 6)) (UInt256.ofNat 6)),
          UInt256.ofNat 0,
          UInt256.shiftLeft (UInt256.shiftRight n (UInt256.ofNat 6))
            (UInt256.ofNat 6),
          UInt256.land (UInt256.ofNat 63) n, n] } := by
  evm_block
''')

    out.append(path("initialBranchPath", located, [1377]))
    out.append('''
theorem run_initialBranch_full (s : State) (endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2464)
    (hcond : ¬ UInt256.isTrue (UInt256.isZero endWord))
    (hstack : s.stack = [UInt256.ofNat 2491, UInt256.isZero endWord,
      UInt256.ofNat 0, endWord, rem, n] ++ rest) :
    runLocatedBlock initialBranchPath s =
      some { s with pc := UInt256.ofNat 2465
        stack := [UInt256.ofNat 0, endWord, rem, n] ++ rest } := by
  evm_block hcap

theorem run_initialBranch_tail (s : State) (endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2464)
    (hcond : UInt256.isTrue (UInt256.isZero endWord))
    (hstack : s.stack = [UInt256.ofNat 2491, UInt256.isZero endWord,
      UInt256.ofNat 0, endWord, rem, n] ++ rest) :
    runLocatedBlock initialBranchPath s =
      some { s with pc := UInt256.ofNat 2491
        stack := [UInt256.ofNat 0, endWord, rem, n] ++ rest } := by
  have hdest : Decode.isValidJumpDest Loop.bytes 2491 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 1394 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2491 = true at h
    exact h
  evm_block hcap
''')

    out.append(path("fullBlockCallPath", located, range(1378, 1386)))
    out.append('''
theorem run_fullBlockCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullBlockCallPath s =
      some { s with pc := UInt256.ofNat 4
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288
        stack := [UInt256.ofNat 2480, off, endWord, rem, n] ++ rest } := by
  have hbody : Decode.isValidJumpDest Loop.bytes 4 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 2 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 4 = true at h
    exact h
  evm_block hcap
''')

    out.append(path("fullLoopTestPath", located, range(1386, 1393)))
    out.append('''
theorem run_fullLoopTest (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2480)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullLoopTestPath s =
      some { s with pc := UInt256.ofNat 2490
        stack := [UInt256.ofNat 2465,
          UInt256.lt (UInt256.ofNat 64 + off) endWord,
          UInt256.ofNat 64 + off, endWord, rem, n] ++ rest } := by
  evm_block hcap
''')

    out.append(path("fullLoopBranchPath", located, [1393]))
    out.append('''
theorem run_fullLoopBranch_continue (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2490)
    (hcond : UInt256.isTrue (UInt256.lt off endWord))
    (hstack : s.stack = [UInt256.ofNat 2465, UInt256.lt off endWord,
      off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullLoopBranchPath s =
      some { s with pc := UInt256.ofNat 2465
        stack := [off, endWord, rem, n] ++ rest } := by
  have hdest : Decode.isValidJumpDest Loop.bytes 2465 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 1378 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2465 = true at h
    exact h
  evm_block hcap

theorem run_fullLoopBranch_exit (s : State)
    (off endWord rem n : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hpc : s.pc = UInt256.ofNat 2490)
    (hcond : ¬ UInt256.isTrue (UInt256.lt off endWord))
    (hstack : s.stack = [UInt256.ofNat 2465, UInt256.lt off endWord,
      off, endWord, rem, n] ++ rest) :
    runLocatedBlock fullLoopBranchPath s =
      some { s with pc := UInt256.ofNat 2491
        stack := [off, endWord, rem, n] ++ rest } := by
  evm_block hcap
''')

    out.append(path("tailPreparePath", located, range(1394, 1408)))
    out.append('''
theorem run_tailPrepare (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2491)
    (hrem : rem.toNat < 64)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock tailPreparePath s =
      some { s with pc := UInt256.ofNat 2514
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes
          (MachineState.writeBytes s.memory
            (MachineState.readPadded s.executionEnv.calldata off.toNat 64) 288)
          (ByteArray.mk #[UInt8.ofNat
            ((UInt256.ofNat 128).toNat % 256)])
          (UInt256.ofNat 288 + rem).toNat
        stack := [UInt256.ofNat 2533,
          UInt256.lt rem (UInt256.ofNat 56), off, endWord, rem, n] ++ rest } := by
  evm_block hcap
  have hadd : (UInt256.ofNat 288 + rem).toNat = 288 + rem.toNat := by
    rw [word_toNat_add, word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    norm_num
  apply congrArg UInt256.ofNat
  norm_num [MachineState.activeWordsAfter, hadd]
  omega
''')

    out.append(path("tailBranchPath", located, [1408]))
    out.append('''
theorem run_tailBranch_short (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2514)
    (hcond : UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hstack : s.stack = [UInt256.ofNat 2533,
      UInt256.lt rem (UInt256.ofNat 56), off, endWord, rem, n] ++ rest) :
    runLocatedBlock tailBranchPath s =
      some { s with pc := UInt256.ofNat 2533
        stack := [off, endWord, rem, n] ++ rest } := by
  have hdest : Decode.isValidJumpDest Loop.bytes 2533 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 1419 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 2533 = true at h
    exact h
  evm_block hcap

theorem run_tailBranch_long (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2514)
    (hcond : ¬ UInt256.isTrue (UInt256.lt rem (UInt256.ofNat 56)))
    (hstack : s.stack = [UInt256.ofNat 2533,
      UInt256.lt rem (UInt256.ofNat 56), off, endWord, rem, n] ++ rest) :
    runLocatedBlock tailBranchPath s =
      some { s with pc := UInt256.ofNat 2515
        stack := [off, endWord, rem, n] ++ rest } := by
  evm_block hcap
''')

    out.append(path("firstTailCallPath", located, range(1409, 1412)))
    out.append('''
theorem run_firstTailCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2515)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock firstTailCallPath s =
      some { s with pc := UInt256.ofNat 4
        stack := [UInt256.ofNat 2522, off, endWord, rem, n] ++ rest } := by
  have hbody : Decode.isValidJumpDest Loop.bytes 4 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 2 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 4 = true at h
    exact h
  evm_block hcap
''')

    out.append(path("clearSecondTailPath", located, range(1412, 1419)))
    out.append('''
theorem run_clearSecondTail (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2522)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock clearSecondTailPath s =
      some { s with pc := UInt256.ofNat 2533
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes
          (MachineState.writeBytes s.memory
            (Data.Bytes.natToBytesPadded 0 32) 288)
          (Data.Bytes.natToBytesPadded 0 32) 320 } := by
  evm_block hcap <;> simp [UInt256.toNat]
''')

    out.append(path("lengthCallPath", located, range(1419, 1432)))
    out.append('''
theorem run_lengthCall (s : State) (off endWord rem n : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2533)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest) :
    runLocatedBlock lengthCallPath s =
      some { s with pc := UInt256.ofNat 4
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded
            (UInt256.shiftLeft
              (UInt256.land (UInt256.ofNat 18446744073709551615)
                (UInt256.shiftLeft n (UInt256.ofNat 3)))
              (UInt256.ofNat 192)).toNat 32) 344
        stack := [UInt256.ofNat 2562, off, endWord, rem, n] ++ rest } := by
  have hbody : Decode.isValidJumpDest Loop.bytes 4 = true := by
    have h := ProgramArtifact.isValidJumpDest_index Loop.art 2 (by rfl)
    change Decode.isValidJumpDest Loop.bytes 4 = true at h
    exact h
  evm_block hcap
''')

    out.append('''
def outputBytes (H0 H1 H2 H3 H4 H5 H6 H7 : UInt32) : ByteArray :=
  Data.Bytes.natToBytesPadded
    (UInt256.lor (ofUInt32 H7)
      (UInt256.lor (UInt256.shiftLeft (ofUInt32 H6) (UInt256.ofNat 32))
        (UInt256.lor (UInt256.shiftLeft (ofUInt32 H5) (UInt256.ofNat 64))
          (UInt256.lor (UInt256.shiftLeft (ofUInt32 H4) (UInt256.ofNat 96))
            (UInt256.lor (UInt256.shiftLeft (ofUInt32 H3) (UInt256.ofNat 128))
              (UInt256.lor (UInt256.shiftLeft (ofUInt32 H2) (UInt256.ofNat 160))
                (UInt256.lor (UInt256.shiftLeft (ofUInt32 H1) (UInt256.ofNat 192))
                  (UInt256.shiftLeft (ofUInt32 H0) (UInt256.ofNat 224))))))))).toNat 32
''')
    out.append("\nend Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverBlocks\n")
    return "".join(out).replace("{ s with pc :=", "{ s with\n        pc :=")


def emit_output():
    code, _ = G.build()
    located = [lean_located(i, ins) for i, ins in enumerate(disassemble(code))]
    out = ['''import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverBlocks

set_option warningAsError false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.OutputBlock

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open YulEvmCompiler Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.EvmProof.Word Challenge.Sha256.Fast
open DriverBlocks

private def wfOp {op : Operation}
    (h1 : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (h2 : YulEvmCompiler.plainOp op) (h3 : op.availableInFork .Osaka = true) :
    WellFormed .Osaka (.op op) := ⟨h1, h2, h3⟩
''']
    out.append(path("outputPath", located, range(1432, 1475)))
    out.append('''
theorem run_output (s : State) (off endWord rem n : UInt256)
    (H0 H1 H2 H3 H4 H5 H6 H7 : UInt32)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2562)
    (hstack : s.stack = [off, endWord, rem, n] ++ rest)
    (hh0 : MachineState.readWord s.memory 32 = ofUInt32 H0)
    (hh1 : MachineState.readWord s.memory 64 = ofUInt32 H1)
    (hh2 : MachineState.readWord s.memory 96 = ofUInt32 H2)
    (hh3 : MachineState.readWord s.memory 128 = ofUInt32 H3)
    (hh4 : MachineState.readWord s.memory 160 = ofUInt32 H4)
    (hh5 : MachineState.readWord s.memory 192 = ofUInt32 H5)
    (hh6 : MachineState.readWord s.memory 224 = ofUInt32 H6)
    (hh7 : MachineState.readWord s.memory 256 = ofUInt32 H7) :
    runLocatedBlock outputPath s =
      some { s with
        pc := UInt256.ofNat 2621
        halt := .Returned
        activeWords := UInt256.ofNat 140
        memory := MachineState.writeBytes s.memory
          (outputBytes H0 H1 H2 H3 H4 H5 H6 H7) 0
        hReturn := outputBytes H0 H1 H2 H3 H4 H5 H6 H7
        stack := [off, endWord, rem, n] ++ rest } := by
  evm_block hcap
  constructor
  · rfl
  · change MachineState.readPadded
        (MachineState.writeBytes s.memory
          (outputBytes H0 H1 H2 H3 H4 H5 H6 H7) 0) 0 32 =
        outputBytes H0 H1 H2 H3 H4 H5 H6 H7
    have hsize : (outputBytes H0 H1 H2 H3 H4 H5 H6 H7).size = 32 := by
      unfold outputBytes
      exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
    rw [← hsize]
    exact Challenge.EvmProof.Memory.readPadded_writeBytes_same s.memory
      (outputBytes H0 H1 H2 H3 H4 H5 H6 H7) 0

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.OutputBlock
''')
    return "".join(out)


if __name__ == "__main__":
    import sys
    with open(sys.argv[1], "w") as output:
        output.write(emit())
    if len(sys.argv) > 2:
        with open(sys.argv[2], "w") as output:
            output.write(emit_output())
