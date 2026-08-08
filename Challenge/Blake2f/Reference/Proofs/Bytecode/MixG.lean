import Challenge.Blake2f.Reference.Proofs.Bytecode.Artifact
import Challenge.Blake2f.ProofSupport.InitialState
import Challenge.Blake2f.ProofSupport.Word
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-!
# Direct trace of the compiled `mixG` helper

The helper is certified independently of its eight call sites. Its memory
transition deliberately uses only EVM word operations; a separate theorem
connects that transition to `Crypto.Blake2f.mixG`.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.MixG

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def prepPath := Artifact.locatedPath
  [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
   90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]

def aPath := Artifact.locatedPath
  [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
def dPath := Artifact.locatedPath
  [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
   129, 130, 131]
def cPath := Artifact.locatedPath
  [132, 133, 134, 135, 136, 137, 138, 139, 140]
def bPath := Artifact.locatedPath
  [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
   154, 155, 156]
def firstPath := aPath ++ dPath ++ cPath ++ bPath

def a2Path := Artifact.locatedPath
  [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168]
def d2Path := Artifact.locatedPath
  [169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181,
   182, 183, 184, 185]
def c2Path := Artifact.locatedPath
  [186, 187, 188, 189, 190, 191, 192, 193, 194, 195]
def b2Path := Artifact.locatedPath
  [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208,
   209, 210, 211, 212]
def secondPath := a2Path ++ d2Path ++ c2Path ++ b2Path

def cleanupPath := Artifact.locatedPath
  [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225,
   226, 227, 228, 229, 230, 231]

def path := prepPath ++ firstPath ++ secondPath ++ cleanupPath

def storeWord (memory : ByteArray) (offset : UInt256) (value : UInt256) :
    ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset.toNat

def rotate (value : UInt256) (amount : Nat) : UInt256 :=
  UInt256.land
    (UInt256.lor
      (UInt256.shiftRight value (UInt256.ofNat amount))
      (UInt256.shiftLeft value (UInt256.ofNat (64 - amount))))
    (UInt256.ofNat 0xffffffffffffffff)

def rowOffset (round : UInt256) : UInt256 :=
  UInt256.ofNat 1536 +
    UInt256.shiftLeft (round % UInt256.ofNat 10) (UInt256.ofNat 5)

def rowWord (memory : ByteArray) (round : UInt256) : UInt256 :=
  MachineState.readWord memory (rowOffset round).toNat

def messageOffset (row column : UInt256) : UInt256 :=
  UInt256.ofNat 256 + UInt256.shiftLeft
    (UInt256.byteAt (UInt256.ofNat 16 + column) row) (UInt256.ofNat 5)

def messageWord (memory : ByteArray) (row column : UInt256) : UInt256 :=
  MachineState.readWord memory (messageOffset row column).toNat

structure FirstStage where
  memory : ByteArray
  va : UInt256
  xd : UInt256
  vd : UInt256
  vc : UInt256
  xb : UInt256
  vb : UInt256

def vaValue (memory : ByteArray) (a b x : UInt256) : UInt256 :=
  UInt256.land
    (MachineState.readWord memory a.toNat +
      MachineState.readWord memory b.toNat + x)
    (UInt256.ofNat 0xffffffffffffffff)

def aMemory (memory : ByteArray) (a va : UInt256) : ByteArray :=
  storeWord memory a va

def xdValue (memory : ByteArray) (d va : UInt256) : UInt256 :=
  UInt256.xor (MachineState.readWord memory d.toNat) va

def vdValue (xd : UInt256) : UInt256 :=
  rotate xd 32

def dMemory (memory : ByteArray) (d vd : UInt256) : ByteArray :=
  storeWord memory d vd

def vcValue (memory : ByteArray) (c vd : UInt256) : UInt256 :=
  UInt256.land (MachineState.readWord memory c.toNat + vd)
    (UInt256.ofNat 0xffffffffffffffff)

def cMemory (memory : ByteArray) (c vc : UInt256) : ByteArray :=
  storeWord memory c vc

def xbValue (memory : ByteArray) (b vc : UInt256) : UInt256 :=
  UInt256.xor (MachineState.readWord memory b.toNat) vc

def vbValue (xb : UInt256) : UInt256 :=
  rotate xb 24

def firstMemory (memory : ByteArray) (b vb : UInt256) : ByteArray :=
  storeWord memory b vb

def firstStage (memory : ByteArray) (a b c d x : UInt256) : FirstStage :=
  let va := vaValue memory a b x
  let memory := aMemory memory a va
  let xd := xdValue memory d va
  let vd := vdValue xd
  let memory := dMemory memory d vd
  let vc := vcValue memory c vd
  let memory := cMemory memory c vc
  let xb := xbValue memory b vc
  let vb := vbValue xb
  let memory := firstMemory memory b vb
  ⟨memory, va, xd, vd, vc, xb, vb⟩

structure SecondStage where
  memory : ByteArray
  va : UInt256
  xd : UInt256
  vd : UInt256
  vc : UInt256
  xb : UInt256
  vb : UInt256

def va2Value (va vb y : UInt256) : UInt256 :=
  UInt256.land (va + vb + y)
    (UInt256.ofNat 0xffffffffffffffff)

def a2Memory (memory : ByteArray) (a va : UInt256) : ByteArray :=
  storeWord memory a va

def xd2Value (vd va : UInt256) : UInt256 :=
  UInt256.xor vd va

def vd2Value (vd va : UInt256) : UInt256 :=
  rotate (xd2Value vd va) 16

def d2Memory (memory : ByteArray) (d vd : UInt256) : ByteArray :=
  storeWord memory d vd

def vc2Value (vc vd : UInt256) : UInt256 :=
  UInt256.land (vc + vd)
    (UInt256.ofNat 0xffffffffffffffff)

def c2Memory (memory : ByteArray) (c vc : UInt256) : ByteArray :=
  storeWord memory c vc

def xb2Value (vb vc : UInt256) : UInt256 :=
  UInt256.xor vb vc

def vb2Value (vb vc : UInt256) : UInt256 :=
  rotate (xb2Value vb vc) 63

def b2Memory (memory : ByteArray) (b vb : UInt256) : ByteArray :=
  storeWord memory b vb

def secondStage (one : FirstStage) (a b c d y : UInt256) : SecondStage :=
  let va := va2Value one.va one.vb y
  let memory := a2Memory one.memory a va
  let xd := xd2Value one.vd va
  let vd := vd2Value one.vd va
  let memory := d2Memory memory d vd
  let vc := vc2Value one.vc vd
  let memory := c2Memory memory c vc
  let xb := xb2Value one.vb vc
  let vb := vb2Value one.vb vc
  let memory := b2Memory memory b vb
  ⟨memory, va, xd, vd, vc, xb, vb⟩

def transition (memory : ByteArray) (a b c d round xColumn yColumn : UInt256) :
    ByteArray :=
  let row := rowWord memory round
  let x := messageWord memory row xColumn
  let y := messageWord memory row yColumn
  (secondStage (firstStage memory a b c d x) a b c d y).memory

def entryState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 96
    stack := [a, b, c, d, round, xColumn, yColumn, returnDest] ++ tail }

def preparedState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  { s with
    pc := UInt256.ofNat 137
    stack := [y, x, row, a, b, c, d, round, xColumn, yColumn, returnDest] ++ tail }

def aState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  { s with
    pc := UInt256.ofNat 157
    stack := [va, y, x, row, a, b, c, d, round, xColumn, yColumn,
      returnDest] ++ tail,
    memory := aMemory s.memory a va }

def dState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  let memory := aMemory s.memory a va
  let xd := xdValue memory d va
  let vd := vdValue xd
  { s with
    pc := UInt256.ofNat 183
    stack := [vd, xd, va, y, x, row, a, b, c, d, round,
      xColumn, yColumn, returnDest] ++ tail,
    memory := dMemory memory d vd }

def cState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  let memory := aMemory s.memory a va
  let xd := xdValue memory d va
  let vd := vdValue xd
  let memory := dMemory memory d vd
  let vc := vcValue memory c vd
  { s with
    pc := UInt256.ofNat 200
    stack := [vc, vd, xd, va, y, x, row, a, b, c, d,
      round, xColumn, yColumn, returnDest] ++ tail,
    memory := cMemory memory c vc }

def firstState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  let memA := aMemory s.memory a va
  let xd := xdValue memA d va
  let vd := vdValue xd
  let memD := dMemory memA d vd
  let vc := vcValue memD c vd
  let memC := cMemory memD c vc
  let xb := xbValue memC b vc
  let vb := vbValue xb
  { s with
    pc := UInt256.ofNat 226
    stack := [vb, xb, vc, vd, xd, va, y, x, row,
      a, b, c, d, round, xColumn, yColumn, returnDest] ++ tail,
    memory := firstMemory memC b vb }

def a2State (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  let memA := aMemory s.memory a va
  let xd := xdValue memA d va
  let vd := vdValue xd
  let memD := dMemory memA d vd
  let vc := vcValue memD c vd
  let memC := cMemory memD c vc
  let xb := xbValue memC b vc
  let vb := vbValue xb
  let memB := firstMemory memC b vb
  let va2 := va2Value va vb y
  { s with
    pc := UInt256.ofNat 246
    stack := [vb, xb, vc, vd, xd, va2,
      y, x, row, a, b, c, d, round, xColumn, yColumn, returnDest] ++ tail,
    memory := a2Memory memB a va2 }

def d2State (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  let memA := aMemory s.memory a va
  let xd := xdValue memA d va
  let vd := vdValue xd
  let memD := dMemory memA d vd
  let vc := vcValue memD c vd
  let memC := cMemory memD c vc
  let xb := xbValue memC b vc
  let vb := vbValue xb
  let memB := firstMemory memC b vb
  let va2 := va2Value va vb y
  let xd2 := xd2Value vd va2
  let vd2 := vd2Value vd va2
  let memory := a2Memory memB a va2
  { s with
    pc := UInt256.ofNat 273
    stack := [xd2, vb, xb, vc, vd2, xd, va2,
      y, x, row, a, b, c, d, round, xColumn,
      yColumn, returnDest] ++ tail,
    memory := d2Memory memory d vd2 }

def c2State (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  let memA := aMemory s.memory a va
  let xd := xdValue memA d va
  let vd := vdValue xd
  let memD := dMemory memA d vd
  let vc := vcValue memD c vd
  let memC := cMemory memD c vc
  let xb := xbValue memC b vc
  let vb := vbValue xb
  let memB := firstMemory memC b vb
  let va2 := va2Value va vb y
  let xd2 := xd2Value vd va2
  let vd2 := vd2Value vd va2
  let vc2 := vc2Value vc vd2
  let memory := a2Memory memB a va2
  let memory := d2Memory memory d vd2
  { s with
    pc := UInt256.ofNat 291
    stack := [xd2, vb, xb, vc2, vd2, xd, va2, y, x, row, a, b, c, d,
      round, xColumn, yColumn, returnDest] ++ tail,
    memory := c2Memory memory c vc2 }

def secondState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  let row := rowWord s.memory round
  let x := messageWord s.memory row xColumn
  let y := messageWord s.memory row yColumn
  let va := vaValue s.memory a b x
  let memA := aMemory s.memory a va
  let xd := xdValue memA d va
  let vd := vdValue xd
  let memD := dMemory memA d vd
  let vc := vcValue memD c vd
  let memC := cMemory memD c vc
  let xb := xbValue memC b vc
  let vb := vbValue xb
  let memB := firstMemory memC b vb
  let va2 := va2Value va vb y
  let xd2 := xd2Value vd va2
  let vd2 := vd2Value vd va2
  let vc2 := vc2Value vc vd2
  let xb2 := xb2Value vb vc2
  let vb2 := vb2Value vb vc2
  let memory := a2Memory memB a va2
  let memory := d2Memory memory d vd2
  let memory := c2Memory memory c vc2
  { s with
    pc := UInt256.ofNat 318
    stack := [xb2, xd2, vb2, xb, vc2, vd2, xd, va2,
      y, x, row, a, b, c, d, round, xColumn, yColumn,
      returnDest] ++ tail
    memory := b2Memory memory b vb2 }

def finalState (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := tail
    memory := transition s.memory a b c d round xColumn yColumn }

private theorem activeWordsAfter_eq (offset : Nat)
    (hoffset : offset + 32 ≤ 58 * 32) :
    MachineState.activeWordsAfter 58 offset 32 = 58 := by
  unfold MachineState.activeWordsAfter
  simp only [OfNat.ofNat, Nat.reduceEqDiff, ↓reduceIte]
  apply Nat.max_eq_left
  have hdiv : (offset + 32 - 1) / 32 < 58 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 32)).2
    omega
  exact Nat.succ_le_of_lt hdiv

theorem run_prep (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1004)
    (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 58)
    (hrow : (rowOffset round).toNat + 32 ≤ 58 * 32)
    (hx : (messageOffset (rowWord s.memory round) xColumn).toNat + 32 ≤ 58 * 32)
    (hy : (messageOffset (rowWord s.memory round) yColumn).toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock prepPath
      (entryState s a b c d round xColumn yColumn returnDest tail) =
        some (preparedState s a b c d round xColumn yColumn returnDest tail) := by
  have hcap8 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap9 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap10 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap11 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap12 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap13 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactiveRow := activeWordsAfter_eq (rowOffset round).toNat hrow
  have hactiveX := activeWordsAfter_eq
    (messageOffset (rowWord s.memory round) xColumn).toNat hx
  have hactiveY := activeWordsAfter_eq
    (messageOffset (rowWord s.memory round) yColumn).toNat hy
  have hactiveRow' := hactiveRow
  simp only [rowOffset] at hactiveRow'
  have hactiveX' := hactiveX
  simp only [rowOffset, rowWord, messageOffset] at hactiveX'
  have hactiveY' := hactiveY
  simp only [rowOffset, rowWord, messageOffset] at hactiveY'
  have hpc99 : UInt256.ofNat 97 + UInt256.ofNat 2 = UInt256.ofNat 99 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 97) (b := 2) (by norm_num)
  have hpc103 : UInt256.ofNat 101 + UInt256.ofNat 2 = UInt256.ofNat 103 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 101) (b := 2) (by norm_num)
  have hpc107 : UInt256.ofNat 104 + UInt256.ofNat 3 = UInt256.ofNat 107 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 104) (b := 3) (by norm_num)
  have hpc113 : UInt256.ofNat 111 + UInt256.ofNat 2 = UInt256.ofNat 113 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 111) (b := 2) (by norm_num)
  have hpc117 : UInt256.ofNat 115 + UInt256.ofNat 2 = UInt256.ofNat 117 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 115) (b := 2) (by norm_num)
  have hpc121 : UInt256.ofNat 118 + UInt256.ofNat 3 = UInt256.ofNat 121 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 118) (b := 3) (by norm_num)
  have hpc127 : UInt256.ofNat 125 + UInt256.ofNat 2 = UInt256.ofNat 127 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 125) (b := 2) (by norm_num)
  have hpc131 : UInt256.ofNat 129 + UInt256.ofNat 2 = UInt256.ofNat 131 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 129) (b := 2) (by norm_num)
  have hpc135 : UInt256.ofNat 132 + UInt256.ofNat 3 = UInt256.ofNat 135 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 132) (b := 3) (by norm_num)
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      prepPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      entryState, preparedState, rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap8, hcap9, hcap10, hcap11, hcap12, hcap13, hrun,
      hactive, activeWordsAfter_eq, hactiveRow, hactiveX, hactiveY,
      hactiveRow', hactiveX', hactiveY', hrow, hx, hy,
      hpc99, hpc103, hpc107, hpc113, hpc117, hpc121, hpc127, hpc131, hpc135,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]
  rw [← hactive]

theorem run_a (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1004)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (ha : a.toNat + 32 ≤ 58 * 32) (hb : b.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock aPath
      (preparedState s a b c d round xColumn yColumn returnDest tail) =
        some (aState s a b c d round xColumn yColumn returnDest tail) := by
  have hcap11 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap12 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap13 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap14 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap15 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap16 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap17 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc146 : UInt256.ofNat 137 + UInt256.ofNat 9 = UInt256.ofNat 146 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 137) (b := 9) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      aPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      preparedState, aState, vaValue, aMemory, storeWord,
      rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap11, hcap12, hcap13, hcap14, hcap15, hcap16, hcap17,
      hrun, hactive, activeWordsAfter_eq, ha, hb, hpc146,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_d (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1004)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (hd : d.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock dPath
      (aState s a b c d round xColumn yColumn returnDest tail) =
        some (dState s a b c d round xColumn yColumn returnDest tail) := by
  have hcap12 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap13 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap14 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap15 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap16 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap17 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc170 : UInt256.ofNat 161 + UInt256.ofNat 9 = UInt256.ofNat 170 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 161) (b := 9) (by norm_num)
  have hpc173 : UInt256.ofNat 171 + UInt256.ofNat 2 = UInt256.ofNat 173 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 171) (b := 2) (by norm_num)
  have hpc177 : UInt256.ofNat 175 + UInt256.ofNat 2 = UInt256.ofNat 177 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 175) (b := 2) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      dPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      aState, dState, vaValue, aMemory, xdValue, vdValue, dMemory,
      storeWord, rotate, rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap12, hcap13, hcap14, hcap15, hcap16, hcap17,
      hrun, hactive, activeWordsAfter_eq, hd,
      hpc170, hpc173, hpc177, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_c (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1004)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (hc : c.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock cPath
      (dState s a b c d round xColumn yColumn returnDest tail) =
        some (cState s a b c d round xColumn yColumn returnDest tail) := by
  have hcap14 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap15 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap16 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap17 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc192 : UInt256.ofNat 183 + UInt256.ofNat 9 = UInt256.ofNat 192 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 183) (b := 9) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      dState, cState, vaValue, aMemory, xdValue, vdValue, dMemory,
      vcValue, cMemory, storeWord, rotate,
      rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap14, hcap15, hcap16, hcap17, hrun,
      hactive, activeWordsAfter_eq, hc, hpc192,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_b (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1004)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (hb : b.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock bPath
      (cState s a b c d round xColumn yColumn returnDest tail) =
        some (firstState s a b c d round xColumn yColumn returnDest tail) := by
  have hcap15 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap16 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap17 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap18 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap19 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap20 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc213 : UInt256.ofNat 204 + UInt256.ofNat 9 = UInt256.ofNat 213 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 204) (b := 9) (by norm_num)
  have hpc216 : UInt256.ofNat 214 + UInt256.ofNat 2 = UInt256.ofNat 216 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 214) (b := 2) (by norm_num)
  have hpc220 : UInt256.ofNat 218 + UInt256.ofNat 2 = UInt256.ofNat 220 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 218) (b := 2) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      bPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      cState, firstState, vaValue, aMemory, xdValue, vdValue, dMemory,
      vcValue, cMemory, xbValue, vbValue, firstMemory, storeWord, rotate,
      rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap15, hcap16, hcap17, hcap18, hcap19, hcap20,
      hrun, hactive, activeWordsAfter_eq, hb,
      hpc213, hpc216, hpc220, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_a2 (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1003)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (ha : a.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock a2Path
      (firstState s a b c d round xColumn yColumn returnDest tail) =
        some (a2State s a b c d round xColumn yColumn returnDest tail) := by
  have hcap17 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap18 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap19 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap20 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap21 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc235 : UInt256.ofNat 226 + UInt256.ofNat 9 = UInt256.ofNat 235 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 226) (b := 9) (by norm_num)
  simp only [firstState, a2State]
  generalize hrowValue : rowWord s.memory round = row at *
  generalize hxValue : messageWord s.memory row xColumn = x at *
  generalize hyValue : messageWord s.memory row yColumn = y at *
  generalize hvaValue : vaValue s.memory a b x = va at *
  generalize hmemA : aMemory s.memory a va = memA at *
  generalize hxdValue : xdValue memA d va = xd at *
  generalize hvdValue : vdValue xd = vd at *
  generalize hmemD : dMemory memA d vd = memD at *
  generalize hvcValue : vcValue memD c vd = vc at *
  generalize hmemC : cMemory memD c vc = memC at *
  generalize hxbValue : xbValue memC b vc = xb at *
  generalize hvbValue : vbValue xb = vb at *
  generalize hmemB : firstMemory memC b vb = memB at *
  generalize hva2Value : va2Value va vb y = va2 at *
  simp only [va2Value] at hva2Value
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      a2Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      va2Value, a2Memory, storeWord,
      rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap17, hcap18, hcap19, hcap20, hcap21, hrun,
      hactive, activeWordsAfter_eq, ha, hpc235, hva2Value,
      List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_d2 (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1002)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (hd : d.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock d2Path
      (a2State s a b c d round xColumn yColumn returnDest tail) =
        some (d2State s a b c d round xColumn yColumn returnDest tail) := by
  have hcap17 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap18 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap19 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap20 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap21 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap22 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc258 : UInt256.ofNat 249 + UInt256.ofNat 9 = UInt256.ofNat 258 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 249) (b := 9) (by norm_num)
  have hpc261 : UInt256.ofNat 259 + UInt256.ofNat 2 = UInt256.ofNat 261 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 259) (b := 2) (by norm_num)
  have hpc265 : UInt256.ofNat 263 + UInt256.ofNat 2 = UInt256.ofNat 265 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 263) (b := 2) (by norm_num)
  simp only [a2State, d2State]
  generalize hrowValue : rowWord s.memory round = row at *
  generalize hxValue : messageWord s.memory row xColumn = x at *
  generalize hyValue : messageWord s.memory row yColumn = y at *
  generalize hvaValue : vaValue s.memory a b x = va at *
  generalize hmemA : aMemory s.memory a va = memA at *
  generalize hxdValue : xdValue memA d va = xd at *
  generalize hvdValue : vdValue xd = vd at *
  generalize hmemD : dMemory memA d vd = memD at *
  generalize hvcValue : vcValue memD c vd = vc at *
  generalize hmemC : cMemory memD c vc = memC at *
  generalize hxbValue : xbValue memC b vc = xb at *
  generalize hvbValue : vbValue xb = vb at *
  generalize hmemB : firstMemory memC b vb = memB at *
  generalize hva2Value : va2Value va vb y = va2 at *
  generalize hmemA2 : a2Memory memB a va2 = memA2 at *
  generalize hxd2Value : xd2Value vd va2 = xd2 at *
  generalize hvd2Value : vd2Value vd va2 = vd2 at *
  simp only [xd2Value] at hxd2Value
  simp only [vd2Value, rotate, xd2Value] at hvd2Value
  rw [hxd2Value] at hvd2Value
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      d2Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      xd2Value, vd2Value, d2Memory, storeWord, rotate,
      rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap17, hcap18, hcap19, hcap20, hcap21, hcap22, hrun,
      hactive, activeWordsAfter_eq, hd, hpc258, hpc261, hpc265,
      hxd2Value, hvd2Value,
      List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_c2 (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1003)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (hc : c.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock c2Path
      (d2State s a b c d round xColumn yColumn returnDest tail) =
        some (c2State s a b c d round xColumn yColumn returnDest tail) := by
  have hcap18 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap19 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap20 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap21 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc282 : UInt256.ofNat 273 + UInt256.ofNat 9 = UInt256.ofNat 282 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 273) (b := 9) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      c2Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      d2State, c2State, va2Value, a2Memory, xd2Value, vd2Value,
      d2Memory, vc2Value, c2Memory, storeWord, rotate,
      rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap18, hcap19, hcap20, hcap21, hrun,
      hactive, activeWordsAfter_eq, hc, hpc282,
      List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_b2 (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1001)
    (hrun : s.halt = .Running) (hactive : s.activeWords = UInt256.ofNat 58)
    (hb : b.toNat + 32 ≤ 58 * 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock b2Path
      (c2State s a b c d round xColumn yColumn returnDest tail) =
        some (secondState s a b c d round xColumn yColumn returnDest tail) := by
  have hcap18 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap19 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap20 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap21 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap22 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap23 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hpc303 : UInt256.ofNat 294 + UInt256.ofNat 9 = UInt256.ofNat 303 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 294) (b := 9) (by norm_num)
  have hpc306 : UInt256.ofNat 304 + UInt256.ofNat 2 = UInt256.ofNat 306 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 304) (b := 2) (by norm_num)
  have hpc310 : UInt256.ofNat 308 + UInt256.ofNat 2 = UInt256.ofNat 310 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat (a := 308) (b := 2) (by norm_num)
  simp (config := { maxSteps := 500000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      b2Path, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      c2State, secondState, va2Value, a2Memory, xd2Value, vd2Value,
      d2Memory, vc2Value, c2Memory, xb2Value, vb2Value, b2Memory,
      storeWord, rotate, rowOffset, rowWord, messageOffset, messageWord,
      State.activeWordsAfterUInt256,
      htail, hcap18, hcap19, hcap20, hcap21, hcap22, hcap23, hrun,
      hactive, activeWordsAfter_eq, hb, hpc303, hpc306, hpc310,
      List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_cleanup (s : State)
    (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1001)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock cleanupPath
      (secondState s a b c d round xColumn yColumn returnDest tail) =
        some (finalState s a b c d round xColumn yColumn returnDest tail) := by
  have hcap18 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap19 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc1 : tail.length + 1 < 1024 := by omega
  have hc2 : tail.length + 2 < 1024 := by omega
  have hc3 : tail.length + 3 < 1024 := by omega
  have hc4 : tail.length + 4 < 1024 := by omega
  have hc5 : tail.length + 5 < 1024 := by omega
  have hc6 : tail.length + 6 < 1024 := by omega
  have hc7 : tail.length + 7 < 1024 := by omega
  have hc8 : tail.length + 8 < 1024 := by omega
  have hc9 : tail.length + 9 < 1024 := by omega
  have hc10 : tail.length + 10 < 1024 := by omega
  have hc11 : tail.length + 11 < 1024 := by omega
  have hc12 : tail.length + 12 < 1024 := by omega
  have hc13 : tail.length + 13 < 1024 := by omega
  have hc14 : tail.length + 14 < 1024 := by omega
  have hc15 : tail.length + 15 < 1024 := by omega
  have hc16 : tail.length + 16 < 1024 := by omega
  have hc17 : tail.length + 17 < 1024 := by omega
  have hc18 : tail.length + 18 < 1024 := by omega
  have hc19 : tail.length + 19 < 1024 := by omega
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cleanupPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      secondState, finalState, transition, secondStage, firstStage,
      vaValue, aMemory, xdValue, vdValue, dMemory, vcValue, cMemory,
      xbValue, vbValue, firstMemory,
      va2Value, a2Memory, xd2Value, vd2Value, d2Memory, vc2Value,
      c2Memory, xb2Value, vb2Value, b2Memory, storeWord, rotate,
      rowOffset, rowWord, messageOffset, messageWord,
      htail, hcap18, hcap19, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
      hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19,
      hrun, hcode, hreturn, Nat.add_assoc,
      List.exchange,
      List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

theorem run (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1001)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hactive : s.activeWords = UInt256.ofNat 58)
    (hrow : (rowOffset round).toNat + 32 ≤ 58 * 32)
    (hx : (messageOffset (rowWord s.memory round) xColumn).toNat + 32 ≤ 58 * 32)
    (hy : (messageOffset (rowWord s.memory round) yColumn).toNat + 32 ≤ 58 * 32)
    (ha : a.toNat + 32 ≤ 58 * 32) (hb : b.toNat + 32 ≤ 58 * 32)
    (hc : c.toNat + 32 ≤ 58 * 32) (hd : d.toNat + 32 ≤ 58 * 32)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (entryState s a b c d round xColumn yColumn returnDest tail) =
        some (finalState s a b c d round xColumn yColumn returnDest tail) := by
  have hp := run_prep s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive hrow hx hy
  have haTrace := run_a s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive ha hb
  have hdTrace := run_d s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive hd
  have hcTrace := run_c s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive hc
  have hbTrace := run_b s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive hb
  have ha2Trace := run_a2 s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive ha
  have hd2Trace := run_d2 s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive hd
  have hc2Trace := run_c2 s a b c d round xColumn yColumn returnDest tail
    (by omega) hrun hactive hc
  have hb2Trace := run_b2 s a b c d round xColumn yColumn returnDest tail
    htail hrun hactive hb
  have hcleanup := run_cleanup s a b c d round xColumn yColumn returnDest
    tail htail hrun hcode hreturn
  have hpa := Challenge.EvmProof.Stepper.runLocatedBlock_append
    prepPath aPath
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (preparedState s a b c d round xColumn yColumn returnDest tail)
    (aState s a b c d round xColumn yColumn returnDest tail)
    hp (by simpa [preparedState] using hrun) haTrace
  have hpad := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath) dPath
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (aState s a b c d round xColumn yColumn returnDest tail)
    (dState s a b c d round xColumn yColumn returnDest tail)
    hpa (by simpa [aState] using hrun) hdTrace
  have hpadc := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath ++ dPath) cPath
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (dState s a b c d round xColumn yColumn returnDest tail)
    (cState s a b c d round xColumn yColumn returnDest tail)
    hpad (by simpa [dState] using hrun) hcTrace
  have hfirst := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath ++ dPath ++ cPath) bPath
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (cState s a b c d round xColumn yColumn returnDest tail)
    (firstState s a b c d round xColumn yColumn returnDest tail)
    hpadc (by simpa [cState] using hrun) hbTrace
  have hfirsta := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath ++ dPath ++ cPath ++ bPath) a2Path
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (firstState s a b c d round xColumn yColumn returnDest tail)
    (a2State s a b c d round xColumn yColumn returnDest tail)
    hfirst (by simpa [firstState] using hrun) ha2Trace
  have hfirstad := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath ++ dPath ++ cPath ++ bPath ++ a2Path) d2Path
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (a2State s a b c d round xColumn yColumn returnDest tail)
    (d2State s a b c d round xColumn yColumn returnDest tail)
    hfirsta (by simpa [a2State] using hrun) hd2Trace
  have hfirstadc := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath ++ dPath ++ cPath ++ bPath ++ a2Path ++ d2Path) c2Path
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (d2State s a b c d round xColumn yColumn returnDest tail)
    (c2State s a b c d round xColumn yColumn returnDest tail)
    hfirstad (by simpa [d2State] using hrun) hc2Trace
  have hsecond := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath ++ dPath ++ cPath ++ bPath ++ a2Path ++ d2Path ++ c2Path)
    b2Path
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (c2State s a b c d round xColumn yColumn returnDest tail)
    (secondState s a b c d round xColumn yColumn returnDest tail)
    hfirstadc (by simpa [c2State] using hrun) hb2Trace
  have hfull := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (prepPath ++ aPath ++ dPath ++ cPath ++ bPath ++ a2Path ++ d2Path ++
      c2Path ++ b2Path) cleanupPath
    (entryState s a b c d round xColumn yColumn returnDest tail)
    (secondState s a b c d round xColumn yColumn returnDest tail)
    (finalState s a b c d round xColumn yColumn returnDest tail)
    hsecond (by simpa [secondState] using hrun) hcleanup
  simpa [path, firstPath, secondPath, List.append_assoc] using hfull

def gasSteps (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1001)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hactive : s.activeWords = UInt256.ofNat 58)
    (hrow : (rowOffset round).toNat + 32 ≤ 58 * 32)
    (hx : (messageOffset (rowWord s.memory round) xColumn).toNat + 32 ≤ 58 * 32)
    (hy : (messageOffset (rowWord s.memory round) yColumn).toNat + 32 ≤ 58 * 32)
    (ha : a.toNat + 32 ≤ 58 * 32) (hb : b.toNat + 32 ≤ 58 * 32)
    (hc : c.toNat + 32 ≤ 58 * 32) (hd : d.toNat + 32 ≤ 58 * 32)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (entryState s a b c d round xColumn yColumn returnDest tail)
      (finalState s a b c d round xColumn yColumn returnDest tail) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · simpa [entryState, Artifact.referenceArtifact] using hcode
  · simpa [entryState, State.fork] using hfork
  · exact run s a b c d round xColumn yColumn returnDest tail htail hrun
      hcode hactive hrow hx hy ha hb hc hd hreturn
  · simpa [entryState] using hrun
  · simpa [entryState] using hnp

theorem path_cost (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1001)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hactive : s.activeWords = UInt256.ofNat 58)
    (hrow : (rowOffset round).toNat + 32 ≤ 58 * 32)
    (hx : (messageOffset (rowWord s.memory round) xColumn).toNat + 32 ≤ 58 * 32)
    (hy : (messageOffset (rowWord s.memory round) yColumn).toNat + 32 ≤ 58 * 32)
    (ha : a.toNat + 32 ≤ 58 * 32) (hb : b.toNat + 32 ≤ 58 * 32)
    (hc : c.toNat + 32 ≤ 58 * 32) (hd : d.toNat + 32 ≤ 58 * 32)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path
      (entryState s a b c d round xColumn yColumn returnDest tail) = 454 := by
  have hpotential := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path 454
    (run s a b c d round xColumn yColumn returnDest tail htail hrun hcode
      hactive hrow hx hy ha hb hc hd hreturn)
    (by simpa [entryState, State.fork] using hfork)
    (by
      intro located hlocated
      have hall : path.all
          (fun item => Challenge.EvmProof.Meter.CopyFree item.instruction) = true := by
        decide
      exact List.all_eq_true.mp hall located hlocated)
    (by decide)
  simpa [entryState, finalState, hactive] using hpotential

@[simp] theorem gasSteps_cost
    (s : State) (a b c d round xColumn yColumn returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1001)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hactive : s.activeWords = UInt256.ofNat 58)
    (hrow : (rowOffset round).toNat + 32 ≤ 58 * 32)
    (hx : (messageOffset (rowWord s.memory round) xColumn).toNat + 32 ≤ 58 * 32)
    (hy : (messageOffset (rowWord s.memory round) yColumn).toNat + 32 ≤ 58 * 32)
    (ha : a.toNat + 32 ≤ 58 * 32) (hb : b.toNat + 32 ≤ 58 * 32)
    (hc : c.toNat + 32 ≤ 58 * 32) (hd : d.toNat + 32 ≤ 58 * 32)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (gasSteps s a b c d round xColumn yColumn returnDest tail htail hrun hcode
      hfork hnp hactive hrow hx hy ha hb hc hd hreturn).cost = 454 := by
  exact path_cost s a b c d round xColumn yColumn returnDest tail htail hrun
    hcode hfork hactive hrow hx hy ha hb hc hd hreturn

end Challenge.Blake2f.Reference.Proofs.Bytecode.MixG
