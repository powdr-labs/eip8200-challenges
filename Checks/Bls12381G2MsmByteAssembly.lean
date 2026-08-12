import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssembly

set_option warningAsError true

open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

example : referenceInstructionBytesChunk 0 = referenceFrozenBytesChunk 0 :=
  referenceInstructionChunk0_bytes

example : referenceInstructionBytesChunk 1 = referenceFrozenBytesChunk 1 :=
  referenceInstructionChunk1_bytes

example : referenceInstructionBytesChunk 2 = referenceFrozenBytesChunk 2 :=
  referenceInstructionChunk2_bytes

example : referenceInstructionBytesChunk 3 = referenceFrozenBytesChunk 3 :=
  referenceInstructionChunk3_bytes

example : referenceInstructionBytesChunk 4 = referenceFrozenBytesChunk 4 :=
  referenceInstructionChunk4_bytes

example : referenceInstructionBytesChunk 5 = referenceFrozenBytesChunk 5 :=
  referenceInstructionChunk5_bytes

example : referenceInstructionBytesChunk 6 = referenceFrozenBytesChunk 6 :=
  referenceInstructionChunk6_bytes

example : referenceInstructionBytesChunk 7 = referenceFrozenBytesChunk 7 :=
  referenceInstructionChunk7_bytes

example : referenceInstructionBytesChunk 8 = referenceFrozenBytesChunk 8 :=
  referenceInstructionChunk8_bytes

example : referenceInstructionBytesChunk 9 = referenceFrozenBytesChunk 9 :=
  referenceInstructionChunk9_bytes

example : referenceInstructionBytesChunk 10 = referenceFrozenBytesChunk 10 :=
  referenceInstructionChunk10_bytes

example : referenceInstructionBytesChunk 11 = referenceFrozenBytesChunk 11 :=
  referenceInstructionChunk11_bytes

example : referenceInstructionBytesChunk 12 = referenceFrozenBytesChunk 12 :=
  referenceInstructionChunk12_bytes

example : referenceInstructionBytesChunk 13 = referenceFrozenBytesChunk 13 :=
  referenceInstructionChunk13_bytes

example : referenceInstructionBytesChunk 14 = referenceFrozenBytesChunk 14 :=
  referenceInstructionChunk14_bytes

example : referenceInstructionBytesChunk 15 = referenceFrozenBytesChunk 15 :=
  referenceInstructionChunk15_bytes

example : referenceInstructionBytesChunk 16 = referenceFrozenBytesChunk 16 :=
  referenceInstructionChunk16_bytes

example : referenceInstructionBytesChunk 17 = referenceFrozenBytesChunk 17 :=
  referenceInstructionChunk17_bytes

example : referenceInstructionBytesChunk 18 = referenceFrozenBytesChunk 18 :=
  referenceInstructionChunk18_bytes

example : referenceInstructionBytesChunk 19 = referenceFrozenBytesChunk 19 :=
  referenceInstructionChunk19_bytes

example : referenceInstructionBytesChunk 20 = referenceFrozenBytesChunk 20 :=
  referenceInstructionChunk20_bytes

example : YulEvmCompiler.assemble referenceInstructions =
    Challenge.Bls12381G2Msm.referenceBytecode :=
  referenceInstructions_assemble

/-- info: 'Challenge.Bls12381G2Msm.Reference.Proofs.Compilation.referenceInstructions_assemble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructions_assemble
