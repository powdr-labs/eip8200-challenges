import Challenge.Ripemd160.ProofSupport.Yul
import Challenge.Ripemd160.Reference.Proofs.Yul.Program
import Challenge.YulProof.EvmState
import YulSemantics.Interp

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Exact RIPEMD-160 source state model

Executable state transformers mirroring this reference program's schedule,
rounds, compression tail, and fixed tables.  Generic Yul interpreter and EVM
memory machinery lives under `Challenge.YulProof`.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Yul.StateModel

open YulSemantics
open YulSemantics.EVM
open Challenge.YulProof.EvmState

def hSetState (st : EvmState) (i v : U256) : EvmState :=
  storeWordAt st (0x20 + i * 32) (v &&& 0xffffffff)

def initHState (st : EvmState) : EvmState :=
  hSetState
    (hSetState
      (hSetState
        (hSetState
          (hSetState st 0 0x67452301)
          1 0xefcdab89)
        2 0x98badcfe)
      3 0x10325476)
    4 0xc3d2e1f0

def tableStores : List (U256 × U256) := [
  (0x4a0, 0x000102030405060708090a0b0c0d0e0f07040d010a060f030c000905020e0b08),
  (0x4c0, 0x030a0e04090f0801020700060d0b050c01090b0a00080c040d03070f0e050602),
  (0x4e0, 0x04000509070c020a0e0103080b060f0d00000000000000000000000000000000),
  (0x500, 0x050e070009020b040d060f08010a030c060b0307000d050a0e0f080c04090102),
  (0x520, 0x0f050103070e06090b080c020a00040d08060401030b0f00050c020d09070a0e),
  (0x540, 0x0c0f0a040105080706020d0e0003090b00000000000000000000000000000000),
  (0x560, 0x0b0e0f0c050807090b0d0e0f060709080706080d0b09070f070c0f090b070d0c),
  (0x580, 0x0b0d06070e090d0f0e080d06050c07050b0c0e0f0e0f0908090e05060806050c),
  (0x5a0, 0x090f050b06080d0c050c0d0e0b08050600000000000000000000000000000000),
  (0x5c0, 0x0809090b0d0f0f050707080b0e0e0c06090d0f070c08090b07070c07060f0d0b),
  (0x5e0, 0x09070f0b0806060e0c0d050e0d0d07050f05080b0e0e060e06090c090c050f08),
  (0x600, 0x08050c090c050e06080d06050f0d0b0b00000000000000000000000000000000),
  (0x620, 0x00000000), (0x640, 0x5a827999), (0x660, 0x6ed9eba1),
  (0x680, 0x8f1bbcdc), (0x6a0, 0xa953fd4e), (0x6c0, 0x50a28be6),
  (0x6e0, 0x5c4dd124), (0x700, 0x6d703ef3), (0x720, 0x7a6d76e9),
  (0x740, 0x00000000)]

def initTablesState (st : EvmState) : EvmState := storeMany st tableStores

def xSetState (st : EvmState) (i v : U256) : EvmState :=
  storeWordAt st (0x2a0 + i * 32) (v &&& 0xffffffff)

def scheduleStepState (msgOff : U256) (st : EvmState) (i : Nat) : EvmState :=
  let off := msgOff + BitVec.ofNat 256 i * 4
  let loaded := touchMemory st off.toNat 32
  xSetState loaded (BitVec.ofNat 256 i) (readLE32Value st.memory off)

def schedulePrefix (msgOff : U256) (st : EvmState) : Nat → EvmState
  | 0 => st
  | i + 1 => scheduleStepState msgOff (schedulePrefix msgOff st i) i

def scheduleState (msgOff : U256) (st : EvmState) : EvmState :=
  schedulePrefix msgOff st 16

structure SourceWorking where
  a : U256
  b : U256
  c : U256
  d : U256
  e : U256
deriving DecidableEq

def sourceF (j : Nat) (x y z : U256) : U256 :=
  match j with
  | 0 => (x ^^^ y) ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => ((x ||| ~~~y) ^^^ z) &&& 0xffffffff
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => (x ^^^ (y ||| ~~~z)) &&& 0xffffffff

def sourceRotl (x n : U256) : U256 :=
  ((x <<< n.toNat) ||| (x >>> (32 - n).toNat)) &&& 0xffffffff

def sourceRound (x : SourceWorking) (j : Nat) (word rotation constant : U256) :
    SourceWorking :=
  let t := (x.a + sourceF j x.b x.c x.d + word + constant) &&& 0xffffffff
  let t := (sourceRotl t rotation + x.e) &&& 0xffffffff
  { a := x.e, b := t, c := x.b, d := sourceRotl x.c 10, e := x.d }

def workingAt (memory : Nat → UInt8) (base : U256) : SourceWorking where
  a := loadWord memory (base + 0 * 32).toNat
  b := loadWord memory (base + 1 * 32).toNat
  c := loadWord memory (base + 2 * 32).toNat
  d := loadWord memory (base + 3 * 32).toNat
  e := loadWord memory (base + 4 * 32).toNat

def storeWorking (st : EvmState) (base : U256) (x : SourceWorking) : EvmState :=
  let st := storeWordAt st (base + 0 * 32) (x.a &&& 0xffffffff)
  let st := storeWordAt st (base + 4 * 32) (x.e &&& 0xffffffff)
  let st := storeWordAt st (base + 3 * 32) (x.d &&& 0xffffffff)
  let st := storeWordAt st (base + 2 * 32) (x.c &&& 0xffffffff)
  storeWordAt st (base + 1 * 32) (x.b &&& 0xffffffff)

def touchWorking (st : EvmState) (base : U256) : EvmState :=
  let st := touchMemory st (base + 0 * 32).toNat 32
  let st := touchMemory st (base + 1 * 32).toNat 32
  let st := touchMemory st (base + 2 * 32).toNat 32
  let st := touchMemory st (base + 3 * 32).toNat 32
  touchMemory st (base + 4 * 32).toNat 32

def roundState (st : EvmState) (base : U256) (j : Nat)
    (wordIndex rotation constant : U256) : EvmState :=
  let x := workingAt st.memory base
  let wordAddress := 0x2a0 + wordIndex * 32
  let readState := touchMemory (touchWorking st base) wordAddress.toNat 32
  let word := loadWord st.memory wordAddress.toNat
  storeWorking readState base (sourceRound x j word rotation constant)

def tableValue (memory : Nat → UInt8) (base i : U256) : U256 :=
  let word := loadWord memory (base + (i / 32) * 32).toNat
  if 32 ≤ i.toNat % 32 then 0 else
    (word >>> (248 - 8 * (i.toNat % 32))) &&& 0xff

def leftRoundStepState (st : EvmState) (i : Nat) : EvmState :=
  let iw := BitVec.ofNat 256 i
  let j := i / 16
  let jw := BitVec.ofNat 256 j
  let constantAddress := 0x620 + jw * 32
  let constantState := touchMemory st constantAddress.toNat 32
  let constant := loadWord st.memory constantAddress.toNat
  let rotationState := touchMemory constantState (0x560 + (iw / 32) * 32).toNat 32
  let rotation := tableValue st.memory 0x560 iw
  let wordState := touchMemory rotationState (0x4a0 + (iw / 32) * 32).toNat 32
  let wordIndex := tableValue st.memory 0x4a0 iw
  roundState wordState 0x0c0 j wordIndex rotation constant

def leftRoundPrefix : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st => leftRoundStepState (leftRoundPrefix i st) i

def rightRoundStepState (st : EvmState) (i : Nat) : EvmState :=
  let iw := BitVec.ofNat 256 i
  let group := i / 16
  let groupWord := BitVec.ofNat 256 group
  let j := 4 - group
  let constantAddress := 0x6c0 + groupWord * 32
  let constantState := touchMemory st constantAddress.toNat 32
  let constant := loadWord st.memory constantAddress.toNat
  let rotationState := touchMemory constantState (0x5c0 + (iw / 32) * 32).toNat 32
  let rotation := tableValue st.memory 0x5c0 iw
  let wordState := touchMemory rotationState (0x500 + (iw / 32) * 32).toNat 32
  let wordIndex := tableValue st.memory 0x500 iw
  roundState wordState 0x160 j wordIndex rotation constant

def rightRoundPrefix : Nat → EvmState → EvmState
  | 0, st => st
  | i + 1, st => rightRoundStepState (rightRoundPrefix i st) i

def compressionWorkState (st : EvmState) (msgOff : U256) : EvmState :=
  let st := scheduleState msgOff st
  let st := mcopyState st 0x0c0 0x020 0x0a0
  let st := mcopyState st 0x160 0x020 0x0a0
  let st := mcopyState st 0x200 0x020 0x0a0
  let st := leftRoundPrefix 80 st
  rightRoundPrefix 80 st

def addThreeMasked (st : EvmState) (p q r : U256) : U256 × EvmState :=
  let sr := touchMemory st r.toNat 32
  let sq := touchMemory sr q.toNat 32
  let sp := touchMemory sq p.toNat 32
  (((loadWord st.memory p.toNat + loadWord st.memory q.toNat) +
    loadWord st.memory r.toNat) &&& 0xffffffff, sp)

def compressionTailState (st : EvmState) : EvmState :=
  let (t, st) := addThreeMasked st 0x220 0x100 0x1c0
  let (h1, st) := addThreeMasked st 0x240 0x120 0x1e0
  let st := hSetState st 1 h1
  let (h2, st) := addThreeMasked st 0x260 0x140 0x160
  let st := hSetState st 2 h2
  let (h3, st) := addThreeMasked st 0x280 0x0c0 0x180
  let st := hSetState st 3 h3
  let (h4, st) := addThreeMasked st 0x200 0x0e0 0x1a0
  let st := hSetState st 4 h4
  hSetState st 0 t

def compressionState (st : EvmState) (msgOff : U256) : EvmState :=
  compressionTailState (compressionWorkState st msgOff)

theorem eval_hAt (fuel : Nat) (st : EvmState) (i : Nat) :
    Interp.evalExpr localExec (fuel + 20) verifiedFunctions [] st
      (.call "hAt" [.lit (.number i)]) =
      .ok (.vals
        [loadWord st.memory
          ((litValue (.number 0x20) + litValue (.number i) * litValue (.number 32)).toNat)]
        (touchMemory st
          ((litValue (.number 0x20) + litValue (.number i) * litValue (.number 32)).toNat) 32)) := by
  rfl

theorem eval_initH (fuel : Nat) (st : EvmState) :
    Interp.evalExpr localExec (fuel + 100) verifiedFunctions [] st (.call "initH" []) =
      .ok (.vals [] (initHState st)) := by
  rfl

end Challenge.Ripemd160.Reference.Proofs.Yul.StateModel
