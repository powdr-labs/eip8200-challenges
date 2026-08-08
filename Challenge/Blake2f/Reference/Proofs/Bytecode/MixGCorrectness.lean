import Challenge.Blake2f.ProofSupport.Memory
import Challenge.Blake2f.Reference.Proofs.Bytecode.MixG

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-! Semantic bridge from the certified `mixG` memory trace to BLAKE2f lanes. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.MixGCorrectness

open Challenge.Blake2f
open Challenge.Blake2f.ProofSupport
open EvmSemantics

private theorem land_eq (x y : UInt256) : UInt256.land x y = x &&& y := rfl
private theorem lor_eq (x y : UInt256) : UInt256.lor x y = x ||| y := rfl
private theorem xor_eq (x y : UInt256) : UInt256.xor x y = x ^^^ y := rfl

@[simp] theorem readWord_storeWord_same (memory : ByteArray) (offset value : UInt256) :
    MachineState.readWord (MixG.storeWord memory offset value) offset.toNat = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset.toNat value

theorem readWord_storeWord_disjoint (memory : ByteArray)
    (readStart writeStart value : UInt256)
    (h : Memory.WordDisjoint readStart.toNat writeStart.toNat) :
    MachineState.readWord (MixG.storeWord memory writeStart value) readStart.toNat =
      MachineState.readWord memory readStart.toNat := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa [Memory.WordDisjoint, Data.Bytes.natToBytesPadded, ByteArray.size] using h

/-- The helper's byte-array transition performs exactly the reusable pure EVM
quarter-round on its four disjoint word lanes. -/
theorem lanesAt_transition (memory : ByteArray)
    (a b c d round xColumn yColumn : UInt256)
    (hab : Memory.WordDisjoint a.toNat b.toNat)
    (hac : Memory.WordDisjoint a.toNat c.toNat)
    (had : Memory.WordDisjoint a.toNat d.toNat)
    (hbc : Memory.WordDisjoint b.toNat c.toNat)
    (hbd : Memory.WordDisjoint b.toNat d.toNat)
    (hcd : Memory.WordDisjoint c.toNat d.toNat) :
    Memory.lanesAtWords
        (MixG.transition memory a b c d round xColumn yColumn)
        a.toNat b.toNat c.toNat d.toNat =
      Algorithm.mixLanesEVM
        (Memory.lanesAtWords memory a.toNat b.toNat c.toNat d.toNat)
        (MixG.messageWord memory (MixG.rowWord memory round) xColumn)
        (MixG.messageWord memory (MixG.rowWord memory round) yColumn) := by
  have hba := Memory.WordDisjoint.symm hab
  have hca := Memory.WordDisjoint.symm hac
  have hda := Memory.WordDisjoint.symm had
  have hcb := Memory.WordDisjoint.symm hbc
  have hdb := Memory.WordDisjoint.symm hbd
  have hdc := Memory.WordDisjoint.symm hcd
  have rab (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m a b v hab
  have rac (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m a c v hac
  have rad (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m a d v had
  have rba (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m b a v hba
  have rbc (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m b c v hbc
  have rbd (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m b d v hbd
  have rca (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m c a v hca
  have rcb (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m c b v hcb
  have rcd (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m c d v hcd
  have rda (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m d a v hda
  have rdb (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m d b v hdb
  have rdc (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m d c v hdc
  apply Algorithm.Lanes.ext <;>
    simp [MixG.transition, MixG.secondStage, MixG.firstStage,
      MixG.vaValue, MixG.aMemory, MixG.xdValue, MixG.vdValue,
      MixG.dMemory, MixG.vcValue, MixG.cMemory, MixG.xbValue,
      MixG.vbValue, MixG.firstMemory, MixG.va2Value, MixG.a2Memory,
      MixG.xd2Value, MixG.vd2Value, MixG.d2Memory, MixG.vc2Value,
      MixG.c2Memory, MixG.xb2Value, MixG.vb2Value, MixG.b2Memory,
      MixG.rotate, Memory.lanesAtWords, Algorithm.mixLanesEVM,
      Algorithm.rotrWord, Challenge.Blake2f.ProofSupport.Word.mask64,
      land_eq, lor_eq, xor_eq,
      rab, rac, rad, rba, rbc, rbd, rca, rcb, rcd, rda, rdb, rdc]

/-- Any word disjoint from the four target lanes is unchanged by the helper.
This is the frame rule used to preserve message words and sigma rows across a
round. -/
theorem readWord_transition_disjoint (memory : ByteArray)
    (readStart a b c d round xColumn yColumn : UInt256)
    (ha : Memory.WordDisjoint readStart.toNat a.toNat)
    (hb : Memory.WordDisjoint readStart.toNat b.toNat)
    (hc : Memory.WordDisjoint readStart.toNat c.toNat)
    (hd : Memory.WordDisjoint readStart.toNat d.toNat) :
    MachineState.readWord
        (MixG.transition memory a b c d round xColumn yColumn)
        readStart.toNat =
      MachineState.readWord memory readStart.toNat := by
  have ra (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m readStart a v ha
  have rb (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m readStart b v hb
  have rc (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m readStart c v hc
  have rd (m : ByteArray) (v : UInt256) :=
    readWord_storeWord_disjoint m readStart d v hd
  simp [MixG.transition, MixG.secondStage, MixG.firstStage,
    MixG.aMemory, MixG.dMemory, MixG.cMemory, MixG.firstMemory,
    MixG.a2Memory, MixG.d2Memory, MixG.c2Memory, MixG.b2Memory,
    ra, rb, rc, rd]

/-- Submission-facing semantic form: once the four memory lanes and the two
message words represent 64-bit algorithm values, the helper agrees with the
pinned array implementation of `Crypto.Blake2f.mixG`. -/
theorem lanesAt_transition_embed (memory : ByteArray) (v : Array UInt64)
    (a b c d round xColumn yColumn : UInt256) (ai bi ci di : Nat)
    (x y : UInt64)
    (hab : Memory.WordDisjoint a.toNat b.toNat)
    (hac : Memory.WordDisjoint a.toNat c.toNat)
    (had : Memory.WordDisjoint a.toNat d.toNat)
    (hbc : Memory.WordDisjoint b.toNat c.toNat)
    (hbd : Memory.WordDisjoint b.toNat d.toNat)
    (hcd : Memory.WordDisjoint c.toNat d.toNat)
    (hlanes : Memory.lanesAtWords memory a.toNat b.toNat c.toNat d.toNat =
      (Algorithm.lanesAt v ai bi ci di).embed)
    (hx : MixG.messageWord memory (MixG.rowWord memory round) xColumn =
      Word.ofUInt64 x)
    (hy : MixG.messageWord memory (MixG.rowWord memory round) yColumn =
      Word.ofUInt64 y)
    (hai : ai < v.size) (hbi : bi < v.size)
    (hci : ci < v.size) (hdi : di < v.size)
    (habi : ai ≠ bi) (haci : ai ≠ ci) (hadi : ai ≠ di)
    (hbci : bi ≠ ci) (hbdi : bi ≠ di) (hcdi : ci ≠ di) :
    Memory.lanesAtWords
        (MixG.transition memory a b c d round xColumn yColumn)
        a.toNat b.toNat c.toNat d.toNat =
      (Algorithm.lanesAt (Crypto.Blake2f.mixG v ai bi ci di x y)
        ai bi ci di).embed := by
  rw [lanesAt_transition memory a b c d round xColumn yColumn
    hab hac had hbc hbd hcd, hlanes, hx, hy,
    Algorithm.mixLanesEVM_embed]
  rw [Algorithm.lanesAt_crypto_mixG v ai bi ci di x y
    hai hbi hci hdi habi haci hadi hbci hbdi hcdi]

/-- Submission-facing whole-array refinement. A bytecode using consecutive
32-byte slots may reuse this theorem for every quarter-round rather than
re-proving target-lane updates and the frame rule. -/
theorem representsAt_transition (memory : ByteArray) (v : Array UInt64)
    (base ai bi ci di : Nat) (round xColumn yColumn : UInt256)
    (x y : UInt64)
    (represents : Memory.RepresentsAt memory base v)
    (hx : MixG.messageWord memory (MixG.rowWord memory round) xColumn =
      Word.ofUInt64 x)
    (hy : MixG.messageWord memory (MixG.rowWord memory round) yColumn =
      Word.ofUInt64 y)
    (hfits : base + 32 * v.size < 2 ^ 256)
    (hai : ai < v.size) (hbi : bi < v.size)
    (hci : ci < v.size) (hdi : di < v.size)
    (habi : ai ≠ bi) (haci : ai ≠ ci) (hadi : ai ≠ di)
    (hbci : bi ≠ ci) (hbdi : bi ≠ di) (hcdi : ci ≠ di) :
    Memory.RepresentsAt
      (MixG.transition memory
        (UInt256.ofNat (base + 32 * ai))
        (UInt256.ofNat (base + 32 * bi))
        (UInt256.ofNat (base + 32 * ci))
        (UInt256.ofNat (base + 32 * di)) round xColumn yColumn)
      base (Crypto.Blake2f.mixG v ai bi ci di x y) := by
  let updated := Crypto.Blake2f.mixG v ai bi ci di x y
  have hsize : updated.size = v.size := Algorithm.crypto_mixG_size _ _ _ _ _ _ _
  have hfit (i : Nat) (hi : i < v.size) : base + 32 * i < 2 ^ 256 := by
    omega
  have htoNat (i : Nat) (hi : i < v.size) :
      (UInt256.ofNat (base + 32 * i)).toNat = base + 32 * i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (hfit i hi)]
  have hab := Memory.wordDisjoint_slots base ai bi habi
  have hac := Memory.wordDisjoint_slots base ai ci haci
  have had := Memory.wordDisjoint_slots base ai di hadi
  have hbc := Memory.wordDisjoint_slots base bi ci hbci
  have hbd := Memory.wordDisjoint_slots base bi di hbdi
  have hcd := Memory.wordDisjoint_slots base ci di hcdi
  have hlanes := lanesAt_transition_embed memory v
    (UInt256.ofNat (base + 32 * ai))
    (UInt256.ofNat (base + 32 * bi))
    (UInt256.ofNat (base + 32 * ci))
    (UInt256.ofNat (base + 32 * di)) round xColumn yColumn ai bi ci di x y
    (by simpa [htoNat ai hai, htoNat bi hbi] using hab)
    (by simpa [htoNat ai hai, htoNat ci hci] using hac)
    (by simpa [htoNat ai hai, htoNat di hdi] using had)
    (by simpa [htoNat bi hbi, htoNat ci hci] using hbc)
    (by simpa [htoNat bi hbi, htoNat di hdi] using hbd)
    (by simpa [htoNat ci hci, htoNat di hdi] using hcd)
    (by simpa [htoNat ai hai, htoNat bi hbi, htoNat ci hci, htoNat di hdi]
      using (Memory.lanesAtWords_of_representsAt represents ai bi ci di
        hai hbi hci hdi))
    hx hy hai hbi hci hdi habi haci hadi hbci hbdi hcdi
  intro i hi
  have hiOld : i < v.size := by simpa [hsize] using hi
  by_cases hia : i = ai
  · subst i
    simpa [Memory.lanesAtWords, Algorithm.lanesAt, Algorithm.Lanes.embed,
      htoNat ai hai] using congrArg Algorithm.Lanes.a hlanes
  by_cases hib : i = bi
  · subst i
    simpa [Memory.lanesAtWords, Algorithm.lanesAt, Algorithm.Lanes.embed,
      htoNat bi hbi] using congrArg Algorithm.Lanes.b hlanes
  by_cases hic : i = ci
  · subst i
    simpa [Memory.lanesAtWords, Algorithm.lanesAt, Algorithm.Lanes.embed,
      htoNat ci hci] using congrArg Algorithm.Lanes.c hlanes
  by_cases hid : i = di
  · subst i
    simpa [Memory.lanesAtWords, Algorithm.lanesAt, Algorithm.Lanes.embed,
      htoNat di hdi] using congrArg Algorithm.Lanes.d hlanes
  have hframe := readWord_transition_disjoint memory
    (UInt256.ofNat (base + 32 * i))
    (UInt256.ofNat (base + 32 * ai))
    (UInt256.ofNat (base + 32 * bi))
    (UInt256.ofNat (base + 32 * ci))
    (UInt256.ofNat (base + 32 * di)) round xColumn yColumn
    (by simpa [htoNat i hiOld, htoNat ai hai] using
      Memory.wordDisjoint_slots base i ai hia)
    (by simpa [htoNat i hiOld, htoNat bi hbi] using
      Memory.wordDisjoint_slots base i bi hib)
    (by simpa [htoNat i hiOld, htoNat ci hci] using
      Memory.wordDisjoint_slots base i ci hic)
    (by simpa [htoNat i hiOld, htoNat di hdi] using
      Memory.wordDisjoint_slots base i di hid)
  rw [htoNat i hiOld] at hframe
  rw [hframe, represents i hiOld]
  exact congrArg Word.ofUInt64
    (Algorithm.crypto_mixG_getElem!_other v ai bi ci di i x y hiOld
      hia hib hic hid).symm

/-- Frame rule for a represented array stored wholly before the helper's four
target words. This keeps message-array invariants reusable across rounds. -/
theorem representsAt_transition_before (memory : ByteArray)
    (values : Array UInt64) (base : Nat)
    (a b c d round xColumn yColumn : UInt256)
    (represents : Memory.RepresentsAt memory base values)
    (hfits : base + 32 * values.size < 2 ^ 256)
    (ha : base + 32 * values.size ≤ a.toNat)
    (hb : base + 32 * values.size ≤ b.toNat)
    (hc : base + 32 * values.size ≤ c.toNat)
    (hd : base + 32 * values.size ≤ d.toNat) :
    Memory.RepresentsAt
      (MixG.transition memory a b c d round xColumn yColumn) base values := by
  intro i hi
  have hslot : base + 32 * i < 2 ^ 256 := by omega
  have hframe := readWord_transition_disjoint memory
    (UInt256.ofNat (base + 32 * i)) a b c d round xColumn yColumn
    (Or.inl (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hslot]
      omega))
    (Or.inl (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hslot]
      omega))
    (Or.inl (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hslot]
      omega))
    (Or.inl (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hslot]
      omega))
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hslot] at hframe
  rw [hframe]
  exact represents i hi

end Challenge.Blake2f.Reference.Proofs.Bytecode.MixGCorrectness
